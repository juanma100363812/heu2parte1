
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;

import org.jacop.core.BooleanVar;
import org.jacop.core.Store;
import org.jacop.jasat.utils.structures.IntVec;
import org.jacop.satwrapper.SatWrapper;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;

public class Seguridad {

	public static final int NUMSERPIENTES = 3;
	public static final boolean DEBUG = false;
	public static final boolean DEBUGCLAUSE = true;

	public static void main(String args[]) throws Exception {
		Store store = new Store();
		SatWrapper satWrapper = new SatWrapper();
		store.impose(satWrapper); /* Importante: sat problem */

		// TODO - cambiar mapa a argumentos
		String ruta = "./mapa.txt"; // args[1];
		char mapa[][];
		BufferedReader br;
		File fr = new File(ruta);
		// System.out.println(fr.getAbsolutePath());
		try {
			// abrimos fichero
			br = new BufferedReader((new FileReader(fr)));

			String linea = "";
			String mapaLeido = "";

			while ((linea = br.readLine()) != null) {
				mapaLeido += linea;
				mapaLeido += '-';
			}

			String lineas[] = mapaLeido.split("-");
			mapa = new char[lineas[0].length()][lineas.length];

			// cargamos el mapa a la matriz

			for (int i = 0; i < lineas.length; i++) {
				for (int j = 0; j < lineas[i].length(); j++) {
					mapa[j][i] = lineas[i].charAt(j);
				}
			}

			br.close();
		} catch (Exception e) {
			System.out.println(e.getMessage());
			throw e;
		}

		// 1. DECLARACION DE VARIABLES

		// Se registran las variables
		int columnas = mapa.length;
		int filas = mapa[0].length;
		int countVacias = 0;
		for (int i = 0; i < columnas; i++) {
			for (int j = 0; j < filas; j++) {
				if (mapa[i][j] == ' ')
					countVacias++;
			}
		}

		// creacion de todos los valores posibles de personaje

		BooleanVar[][] personajeXY = new BooleanVar[columnas][filas];

		BooleanVar[][] serpienteXY = new BooleanVar[columnas][filas];

		for (int i = 0; i < columnas; i++) {
			for (int j = 0; j < filas; j++) {
				if (mapa[i][j] == ' ') {
					personajeXY[i][j] = new BooleanVar(store, "\n Node a" + i + "/" + j);
					serpienteXY[i][j] = new BooleanVar(store, "\n Node s" + i + "/" + j);
					satWrapper.register(personajeXY[i][j]);
					satWrapper.register(serpienteXY[i][j]);

				}
			}
		}

		// Todas las variables en un unico array para despues invocar al metodo que nos
		// permite resolver el problema

		BooleanVar allVariablesHastaCuenca[] = new BooleanVar[countVacias * 2];
		int posicion = 0;
		for (int i = 0; i < columnas; i++) {
			for (int j = 0; j < filas; j++) {
				if (personajeXY[i][j] != null) {
					allVariablesHastaCuenca[posicion] = personajeXY[i][j];
					allVariablesHastaCuenca[posicion + countVacias] = serpienteXY[i][j];
					posicion++;
				}
			}

		}

		// 2. DECLARACION DE LOS LITERALES

		int aLiteral[][] = new int[columnas][filas];
		int sLiteral[][][] = new int[countVacias][columnas][filas];
		int aux = 0;

		for (int i = 0; i < columnas; i++) {
			for (int j = 0; j < filas; j++) {
				if (personajeXY[i][j] != null) {
					aLiteral[i][j] = satWrapper.cpVarToBoolVar(personajeXY[i][j], 1, true);
					sLiteral[aux++][i][j] = satWrapper.cpVarToBoolVar(serpienteXY[i][j], 1, true);
				}
			}
		}

		// ver el entero que correspondes a cada literal por posiciones
		if (DEBUG) {
			// sacos pjs y serpientes en mapa
			for (int i = 0; i < aLiteral.length; i++) {
				for (int j = 0; j < aLiteral[i].length; j++) {
					if (aLiteral[i][j] != 0)
						System.out.print(" " + i + "/" + j + ":" + aLiteral[i][j] + " | ");
				}
				System.out.println("");
			}
			for (int index = 0; index < sLiteral.length; index++) {
				for (int i = 0; i < sLiteral[index].length; i++) {
					for (int j = 0; j < sLiteral[index][i].length; j++) {
						if (sLiteral[index][i][j] != 0)
							System.out.print(i + "/" + j + ":" + sLiteral[index][i][j] + " | ");
					}

				}
				System.out.println("");
			}

		}

		// 3. RESTRICCIONES

		/*
		 * El problema se va a definir en forma CNF, por lo tanto, tenemos que añadir
		 * una a una todas las clausulas del problema. Cada clausula será una
		 * disjunción de literales. Por ello, sólo utilizamos los literales
		 * anteriormente obtenidos. Si fuese necesario utilizar un literal negado, éste
		 * se indica con un signo negativo delante. Ejemplo: -xLiteral
		 */

		/* Aristas */

		/* Por cada arista una clausula de los literales involucrados */

		/************************************
		 * tener un muñeco en el mapa
		 **********************************/

		for (int j = 0; j < filas; j++) {
			for (int i = 0; i < columnas; i++) {
				if (aLiteral[i][j] != 0) {

					for (int j2 = 0; j2 < filas; j2++) {
						for (int i2 = i; i2 < columnas; i2++) {
							if (aLiteral[i2][j2] != 0 && aLiteral[i2][j2] != aLiteral[i][j]) {
								/* (-A00 v -A01) ^ (-A00 v -A02 ).... // (-A01 v -A00).... */
								addClause(satWrapper, -aLiteral[i][j], -aLiteral[i2][j2]);
							}
						}
					}

				}
			}
		}
		/* (A00 v A01 v A02 v A03 ...).... */
		addClause(satWrapper, aLiteral, true);

		System.out.println("-------------- fin 1 solo mu�eco en mapa");

		/************************************************************
		 * Serpientes no estan en la misma fila que otras
		 ***********************************************************/

		for (int j = 0; j < filas; j++) {

			for (int i = 0; i < columnas; i++) {

				for (int index = 0; index < sLiteral.length; index++) {
					for (int index2 = 0; index2 < sLiteral.length; index2++) {
						for (int i2 = i + 1; i2 < columnas; i2++) {

							if (sLiteral[index][i][j] != 0 && sLiteral[index2][i2][j] != 0) {

								 addClause(satWrapper, -sLiteral[index][i][j], -sLiteral[index2][i2][j]);

							}

						}

					}
				}

			}

		}

		System.out.println("-------------fin no serpientes misma fila");

		/*************************************************************
		 * Serpientes no pueden estar en misma fila o columna que personaje
		 *************************************************************/

		for (int index = 0; index < sLiteral.length; index++) {
			for (int i = 0; i < sLiteral[index].length; i++) {
				for (int j = 0; j < sLiteral[index][i].length; j++) {
					// si existe la serpiente

					if (sLiteral[index][i][j] != 0) {
						/*
						 * no en la misma fila
						 */
						for (int i2 = 0; i2 < aLiteral.length; i2++) {
							if (aLiteral[i2][j] != 0) {
								 addClause(satWrapper, -sLiteral[index][i][j], -aLiteral[i2][j]);

							}
						}

						/*
						 * No en la misma columna
						 */
						for (int j2 = 0; j2 < aLiteral[i].length; j2++) {
							if (aLiteral[i][j2] != 0 && j2 != j) {
								 addClause(satWrapper, -sLiteral[index][i][j], -aLiteral[i][j2]);
							}
						}

					}

				}
			}

		}

		System.out.println("-------------- fin no serpiente con mu�eco en fila o columna");

		/**************************
		 * Meter las n serpientes contando que no pueden estar en la misma fila
		 **************************/

		for (int j = 0; j < filas; j++) {
			for (int i = 0; i < columnas; i++) {
				for (int index = 0; index < sLiteral.length; index++) {
					if (sLiteral[index][i][j] != 0) {
						int[] serp = new int[countVacias];
						int auxS = 0;
						serp[auxS++] = sLiteral[index][i][j];
						for (int j2 = 0; j2 < filas; j2++) {
							for (int index2 = 0; index2 < sLiteral.length; index2++) {
								for (int i2 = 0; i2 < columnas; i2++) {
									// si misma fila fuera
									if (sLiteral[index2][i2][j2] != 0  && j != j2) { 
										serp[auxS++] = sLiteral[index2][i2][j2];
									}
								}
							}
						}
						if (auxS > 0) {
							addClause(satWrapper, serp, true);
						}
					}
				}
			}
		}
		
		
		
		
		
		
		int[] serp = new int[countVacias];
		aux = 0;
		for (int index = 0; index < sLiteral.length; index++) {
			for (int i = 0; i < columnas; i++) {
				for (int j = 0; j < filas; j++) {
					if(sLiteral[index][i][j]!=0) {
						serp[aux++]=sLiteral[index][i][j];
					}
				}
			}
		}
		
		//addClause(satWrapper, serp, NUMSERPIENTES);
		

		System.out.println("-------------- fin meter n serpientes");

		// 4. INVOCAR AL SOLUCIONADOR

		Search<BooleanVar> search = new DepthFirstSearch<BooleanVar>();
		SelectChoicePoint<BooleanVar> select = new SimpleSelect<BooleanVar>(allVariablesHastaCuenca,
				new SmallestDomain<BooleanVar>(), new IndomainMin<BooleanVar>());
		Boolean result = search.labeling(store, select);

		if (result) {
			System.out.println("Solution: ");
			for (int i = 0; i < personajeXY.length; i++) {
				for (int j = 0; j < personajeXY[i].length; j++) {
					if (personajeXY[i][j] != null) {
						System.out.print(personajeXY[i][j].id() + " " + personajeXY[i][j].value());
						if (personajeXY[i][j].value() == 1)
							mapa[i][j] = 'A';
					}
					if (serpienteXY[i][j] != null) {
						System.out.print(serpienteXY[i][j].id() + " " + serpienteXY[i][j].value());
						if (serpienteXY[i][j].value() == 1)
							mapa[i][j] = 'S';
					}

				}
			}

		} else {
			System.out.println("*** No solution");
		}

		System.out.println("\n-----------------mapa--------------");
		for (int i = 0; i < filas; i++) {
			for (int j = 0; j < columnas; j++) {
				System.out.print(mapa[j][i]);
			}
			System.out.println("");

		}

		System.out.println("-----------------------------------");

	}// fin main

	public static void addClause(SatWrapper satWrapper, int literal1, int literal2) {
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		clause.add(literal2);
		if (DEBUGCLAUSE)
			System.out.println("2 literales :" + clause.toString());
		satWrapper.addModelClause(clause.toArray());
	}

	public static void addClause(SatWrapper satWrapper, int[][] literals, boolean b) {
		IntVec clause = new IntVec(satWrapper.pool);
		for (int i = 0; i < literals.length; i++) {
			for (int j = 0; j < literals[i].length; j++) {
				if (literals[i][j] != 0)
					clause.add(b == true ? literals[i][j] : -literals[i][j]);
			}

		}
		if (DEBUGCLAUSE)
			System.out.println("[][]+bolean:" + clause.toString());
		satWrapper.addModelClause(clause.toArray());
	}

	public static void addClause(SatWrapper satWrapper, int[] literals, boolean b) {
		IntVec clause = new IntVec(satWrapper.pool);
		for (int i = 0; i < literals.length; i++) {
			if (literals[i] != 0)
				clause.add(b ? literals[i] : -literals[i]);

		}
		if (DEBUGCLAUSE)
			System.out.println("[]+boolean: " + clause.toString());

		satWrapper.addModelClause(clause.toArray());
	}

	public static void addClause(SatWrapper satWrapper, int[] literals, int numeroSerpientes) {
		 
		int posClausula[] = new int[numeroSerpientes]; // array clausulas de serpiente a a�adir
		// System.out.println("literales " + literals.length);
		sacarPosiciones(satWrapper, literals, posClausula, numeroSerpientes, 0, 0, true);
		// System.out.println("literales " + literals.length);
		 //posClausula = new int[++numeroSerpientes];
		// sacarPosiciones(satWrapper, literals, posClausula, numeroSerpientes, 0, 0, false);

	}

	// cada posicion recorre todo hasta el ultimo posible en ella
	/*
	 * 1 2 3 1 2 4 1 2 5 1 2 6 1 3 4 1 3 5 .... 4 5 6
	 */
	private static void sacarPosiciones(SatWrapper satWrapper, int[] literals, int[] clausulas, int num, int index,
			int pos, boolean tipo) {
		// clausula llena a meter
		if (index == num) {

			// for (int j = 0; j < num; j++)
			// System.out.print(clausulas[j] + "v");
			// System.out.println("");

			addClause(satWrapper, clausulas, tipo);
			return;
		}

		// ya se ha llenado los elementos de la clausula salimos
		if (pos >= literals.length)
			return;

		// metemos elemento y vamos al siguiente evitando duplicados 1-2 2-1

		clausulas[index] = literals[pos];
		sacarPosiciones(satWrapper, literals, clausulas, num, index + 1, pos + 1, tipo);

		// metemos elemento y vamos al siguiente
		sacarPosiciones(satWrapper, literals, clausulas, num, index, pos + 1, tipo);

	}

}
