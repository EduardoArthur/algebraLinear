#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#define N 15
#define MAX_ITER 1000000

typedef long double tipoPrimitivo; 

tipoPrimitivo tolerancia = 1e-6;

// Hx = b
// Funcao para inicializar a Matriz de Hilbert e os vetores do sistema
void inicializaMatrizHilbert(tipoPrimitivo hilbert[N][N], tipoPrimitivo b[N], tipoPrimitivo xSolucao[N]) {

    // PASSO 1: Gabarito
    for (int i = 0; i < N; i++) {
        xSolucao[i] = 1.0;
        b[i] = 0.0;
    }

    // PASSO 2: Geracao da Matriz de Hilbert
    for (int i = 0; i < N; i++) {
        hilbert[i][i] = 1.0 / (tipoPrimitivo)(2 * i + 1);

        for (int j = i + 1; j < N; j++) {
            hilbert[i][j] = 1.0 / (tipoPrimitivo)(i + j + 1);
            hilbert[j][i] = hilbert[i][j];
        }
    }

    // PASSO 3: Gerar o vetor b (b = hilbert * xSolucao)
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            b[i] = b[i] + (hilbert[i][j] * xSolucao[j]);
        }
    }
}

// Imprime o erro maximo (Norma Infinito)
void imprimeErro(const char* metodo, tipoPrimitivo x[N], tipoPrimitivo xSolucao[N]) {
    tipoPrimitivo erroMax = 0.0;
    for(int i = 0; i < N; i++) {
        tipoPrimitivo erroAtual = fabs(x[i] - xSolucao[i]);
        if(erroAtual > erroMax) {
            erroMax = erroAtual;
        }
    }
    printf("%-15s | Erro Max: %.15f\n", metodo, (double)erroMax);
}

// 1. Eliminacao de Gauss
void eliminacaoGauss(tipoPrimitivo hilbert[N][N], tipoPrimitivo b[N], tipoPrimitivo x[N]) {
    tipoPrimitivo a[N][N];
    tipoPrimitivo bMod[N];

    // Preserva a matriz original e o vetor b
    for (int i = 0; i < N; i++) {
        bMod[i] = b[i];
        for (int j = 0; j < N; j++) {
            a[i][j] = hilbert[i][j];
        }
    }

    // PASSO 1: ELIMINACAO PROGRESSIVA
    // Zera os elementos abaixo da diagonal principal
    for (int k = 0; k < N - 1; k++) {
        for (int i = k + 1; i < N; i++) {
            tipoPrimitivo m = -a[i][k] / a[k][k];
            for (int j = k + 1; j < N; j++) {
                a[i][j] = a[i][j] + m * a[k][j];
            }
            bMod[i] = bMod[i] + m * bMod[k];
        }
    }

    // PASSO 2: SUBSTITUICAO RETROATIVA
    // Encontra o vetor solucao x de baixo para cima
    x[N - 1] = bMod[N - 1] / a[N - 1][N - 1];

    for (int i = N - 2; i >= 0; i--) {
        tipoPrimitivo sum = 0.0;

        // Multiplica os coeficientes pelos 'x' ja descobertos
        for (int j = i + 1; j < N; j++) {
            sum = sum + a[i][j] * x[j];
        }

        // Isola o 'x' atual
        x[i] = (bMod[i] - sum) / a[i][i];
    }
}

// 2. Gauss-Jordan
void gaussJordan(tipoPrimitivo hilbert[N][N], tipoPrimitivo b[N], tipoPrimitivo x[N]) {
    tipoPrimitivo a[N][N], bMod[N];

    // Preserva a matriz original e o vetor b
    for(int i = 0; i < N; i++) {
        bMod[i] = b[i];
        for(int j = 0; j < N; j++) {
            a[i][j] = hilbert[i][j];
        }
    }

    // PASSO 1: ELIMINACAO TOTAL
    // Zera os elementos acima e abaixo do pivo
    for (int k = 0; k < N; k++) {
        for (int i = 0; i < N; i++) {
            // Zera apenas se nao for a linha do proprio pivo
            if (i != k) {
                tipoPrimitivo m = -a[i][k] / a[k][k];
                for (int j = k + 1; j < N; j++) {
                    a[i][j] = a[i][j] + m * a[k][j];
                }
                bMod[i] = bMod[i] + m * bMod[k];
            }
        }
    }

    // PASSO 2: CALCULO DA SOLUCAO
    // A matriz se tornou diagonal. Basta dividir o termo independente pelo pivo.
    for (int i = 0; i < N; i++) {
        x[i] = bMod[i] / a[i][i];
    }
}

// 3. Decomposicao LU
void decomposicaoLU(tipoPrimitivo hilbert[N][N], tipoPrimitivo bOrig[N], tipoPrimitivo x[N]) {
    tipoPrimitivo A[N][N];
    tipoPrimitivo b[N];
    tipoPrimitivo y[N]; // Vetor intermediario para a substituicao sucessiva
    int pivot[N];
    tipoPrimitivo det = 1.0;

    // Preserva a matriz original e o vetor b
    for (int i = 0; i < N; i++) {
        b[i] = bOrig[i];
        for (int j = 0; j < N; j++) {
            A[i][j] = hilbert[i][j];
        }
    }

    // PASSO 1: FATORACAO LU (COM PIVOTEAMENTO PARCIAL)
    for (int i = 0; i < N; i++) {
        pivot[i] = i;
    }

    for (int j = 0; j < N - 1; j++) {
        int p = j;
        tipoPrimitivo Amax = fabs(A[j][j]);

        for (int k = j + 1; k < N; k++) {
            if (fabs(A[k][j]) > Amax) {
                Amax = fabs(A[k][j]);
                p = k;
            }
        }

        if (p != j) {
            for (int k = 0; k < N; k++) {
                tipoPrimitivo t = A[j][k];
                A[j][k] = A[p][k];
                A[p][k] = t;
            }
            int m = pivot[j];
            pivot[j] = pivot[p];
            pivot[p] = m;
            det = -det;
        }

        det = det * A[j][j];

        if (fabs(A[j][j]) != 0.0) {
            tipoPrimitivo r = 1.0 / A[j][j];
            for (int i = j + 1; i < N; i++) {
                tipoPrimitivo Mult = A[i][j] * r;
                A[i][j] = Mult; // Armazena os multiplicadores (Matriz L)

                for (int k = j + 1; k < N; k++) {
                    A[i][k] = A[i][k] - (Mult * A[j][k]); // Atualiza o restante (Matriz U)
                }
            }
        }
    }
    det = det * A[N - 1][N - 1];

    // PASSO 2: SUBSTITUICOES SUCESSIVAS PIVOTAL
    // Resolve Ly = Pb
    int k = pivot[0];
    y[0] = b[k];

    for (int i = 1; i < N; i++) {
        tipoPrimitivo sum = 0.0;
        for (int j = 0; j < i; j++) {
            sum = sum + A[i][j] * y[j];
        }
        k = pivot[i];
        y[i] = b[k] - sum;
    }

    // PASSO 3: RETRO-SUBSTITUICAO
    // Resolve Ux = y
    x[N - 1] = y[N - 1] / A[N - 1][N - 1];

    for (int i = N - 2; i >= 0; i--) {
        tipoPrimitivo sum = 0.0;
        for (int j = i + 1; j < N; j++) {
            sum = sum + A[i][j] * x[j];
        }
        x[i] = (y[i] - sum) / A[i][i];
    }
}

// 4. Gauss-Seidel
void gaussSeidel(tipoPrimitivo hilbert[N][N], tipoPrimitivo bOrig[N], tipoPrimitivo x[N], int ITERMAX, tipoPrimitivo Tol) {
    tipoPrimitivo A[N][N];
    tipoPrimitivo b[N];
    int k = 0;
    tipoPrimitivo erro = INFINITY;
    tipoPrimitivo xant;

    // Preserva a matriz original e o vetor b
    for (int i = 0; i < N; i++) {
        b[i] = bOrig[i];
        for (int j = 0; j < N; j++) {
            A[i][j] = hilbert[i][j];
        }
    }

    // PASSO 1: INICIALIZACAO
    // Define o chute inicial como zero
    for(int i = 0; i < N; i++) {
        x[i] = 0.0;
    }

    // PASSO 2: ITERACOES
    while (k < ITERMAX && erro >= Tol) {
        erro = 0.0;

        for (int i = 0; i < N; i++) {
            xant = x[i];
            tipoPrimitivo sum = 0.0;

            // Somatoria dos elementos da linha atual
            for (int j = 0; j < N; j++) {
                if (j != i) {
                    sum = sum + A[i][j] * x[j];
                }
            }

            // Calcula o novo valor de x
            x[i] = (b[i] - sum) / A[i][i];

            // Verifica o maior erro (diferenca entre iteracoes)
            if (fabs(x[i] - xant) > erro) {
                erro = fabs(x[i] - xant);
            }
        }

        k = k + 1;
    }

    if (erro < Tol) {
        printf("Gauss-Seidel convergiu em %d iteracoes. Erro final: %e\n", k, (tipoPrimitivo)erro);
    } else {
        printf("Gauss-Seidel: Nao houve convergencia em %d iteracoes. Erro final: %e\n", ITERMAX, (tipoPrimitivo)erro);
    }
}

// 5. Jacobi
void jacobi(tipoPrimitivo hilbert[N][N], tipoPrimitivo bOrig[N], tipoPrimitivo x[N], int ITERMAX, tipoPrimitivo Tol) {
    tipoPrimitivo A[N][N];
    tipoPrimitivo b[N];
    tipoPrimitivo x_ant[N];
    int k = 0;
    tipoPrimitivo erro = INFINITY;

    // Preserva a matriz original e o vetor b
    for (int i = 0; i < N; i++) {
        b[i] = bOrig[i];
        for (int j = 0; j < N; j++) {
            A[i][j] = hilbert[i][j];
        }
    }

    // PASSO 1: INICIALIZACAO
    // Define o chute inicial como zero
    for(int i = 0; i < N; i++) {
        x[i] = 0.0;
    }

    // PASSO 2: ITERACOES
    while (k < ITERMAX && erro >= Tol) {
        erro = 0.0;

        // Guarda os valores da iteracao anterior
        for (int i = 0; i < N; i++) {
            x_ant[i] = x[i];
        }

        for (int i = 0; i < N; i++) {
            tipoPrimitivo sum = 0.0;

            // Somatoria baseada unicamente nos valores da iteracao anterior
            for (int j = 0; j < N; j++) {
                if (j != i) {
                    sum = sum + A[i][j] * x_ant[j];
                }
            }

            // Calcula o novo valor de x
            x[i] = (b[i] - sum) / A[i][i];

            // Verifica o maior erro
            if (fabs(x[i] - x_ant[i]) > erro) {
                erro = fabs(x[i] - x_ant[i]);
            }
        }

        k = k + 1;
    }

    if (erro < Tol) {
        printf("Jacobi convergiu em %d iteracoes. Erro final: %e\n", k, (tipoPrimitivo)erro);
    } else {
        printf("Jacobi: Nao houve convergencia em %d iteracoes. Erro final: %e\n", ITERMAX, (tipoPrimitivo)erro);
    }
}

// 6. SOR (Successive Over-Relaxation)
void sor(tipoPrimitivo hilbert[N][N], tipoPrimitivo bOrig[N], tipoPrimitivo x[N], int ITERMAX, tipoPrimitivo Tol, tipoPrimitivo Omega) {
    tipoPrimitivo A[N][N];
    tipoPrimitivo b[N];
    tipoPrimitivo v[N]; // Vetor auxiliar (v) do pseudocodigo
    int iter = 0;
    tipoPrimitivo NormaRel = 1.0;

    // Preserva a matriz original e o vetor b
    for (int i = 0; i < N; i++) {
        b[i] = bOrig[i];
        for (int j = 0; j < N; j++) {
            A[i][j] = hilbert[i][j];
        }
    }

    // PASSO 1: CONSTRUCAO DAS MATRIZES
    for (int i = 0; i < N; i++) {
        tipoPrimitivo r = 1.0 / A[i][i];
        for (int j = 0; j < N; j++) {
            if (i != j) {
                A[i][j] = A[i][j] * r;
            }
        }
        b[i] = b[i] * r;
        x[i] = b[i];
    }

    // PASSO 2: ITERACOES DA SOBRE-RELAXACAO
    do {
        iter++;

        for (int i = 0; i < N; i++) {
            tipoPrimitivo sum = 0.0;

            for (int j = 0; j < N; j++) {
                if (i != j) {
                    sum = sum + (A[i][j] * x[j]);
                }
            }
            v[i] = x[i];

            // Aplica o fator de relaxacao Omega
            x[i] = Omega * (b[i] - sum) + (1.0 - Omega) * x[i];
        }

        tipoPrimitivo NormaNum = 0.0;
        tipoPrimitivo NormaDen = 0.0;

        // Calculo da Norma Relativa
        for (int i = 0; i < N; i++) {
            tipoPrimitivo t = fabs(x[i] - v[i]);
            if (t > NormaNum) {
                NormaNum = t;
            }
            if (fabs(x[i]) > NormaDen) {
                NormaDen = fabs(x[i]);
            }
        }

        NormaRel = NormaNum / NormaDen;

    } while (NormaRel > Tol && iter < ITERMAX);

    if (NormaRel <= Tol) {
        printf("SOR convergiu em %d iteracoes.\n", iter);
    } else {
        printf("SOR: Nao convergiu (Atingiu o limite de %d iteracoes).\n", ITERMAX);
    }
}

int main() {

    tipoPrimitivo hilbert[N][N], b[N], xSolucao[N], x[N];

    inicializaMatrizHilbert(hilbert, b, xSolucao);
    printf("Resolvendo Sistema de Ordem %d com Matriz de Hilbert\n", N);
    printf("----------------------------------------------------\n");

    eliminacaoGauss(hilbert, b, x);
    imprimeErro("Gauss", x, xSolucao);

    gaussJordan(hilbert, b, x);
    imprimeErro("Gauss-Jordan", x, xSolucao);

    decomposicaoLU(hilbert, b, x);
    imprimeErro("LU", x, xSolucao);

    jacobi(hilbert, b, x, MAX_ITER, tolerancia);
    imprimeErro("Jacobi", x, xSolucao);

    gaussSeidel(hilbert, b, x, MAX_ITER, tolerancia);
    imprimeErro("Gauss-Seidel", x, xSolucao);

    sor(hilbert, b, x, MAX_ITER, tolerancia, 1.25);
    imprimeErro("SOR", x, xSolucao);

    return 0;
}