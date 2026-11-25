/*
 * TRABALHO: LABIRINTO COMO GRAFO (BUSCA EM LARGURA E DIJKSTRA)
 *
 * DECISOES E JUSTIFICATIVAS
 *
 * a) Dimensoes: LINHAS = 25 e COLUNAS = 71. O labirinto e o vetor de
 *    strings "lab", escrito no proprio codigo. Sao os unicos pontos que
 *    mudam quando o labirinto muda.
 *
 * b) Validacao: cada linha precisa ter exatamente COLUNAS caracteres
 *    (o '\0' deve estar na posicao COLUNAS e em nenhuma antes), so podem
 *    aparecer ' ', '~', '#', 'E' e 'S', e precisa haver exatamente uma E
 *    e uma S. Se algo falhar, o programa informa e nao executa as buscas.
 *
 * c) Vizinhos examinados na ordem: cima, direita, baixo, esquerda.
 *    Desempate do Dijkstra: entre casas com a mesma distancia, escolhe-se
 *    a de menor numero (linha * COLUNAS + coluna), pois a varredura usa
 *    "<" estrito e comeca da casa 0.
 *
 * d) Representacao do grafo: GRADE COMO GRAFO IMPLICITO. Vertice = casa
 *    que nao e parede, numerada por linha * COLUNAS + coluna. Os vizinhos
 *    sao calculados na hora com dois vetores de deslocamento. Motivo:
 *    sao 1.775 casas e no maximo 4 vizinhos por casa; uma matriz de pesos
 *    teria 1.775 x 1.775 (mais de 3 milhoes) de posicoes, quase todas
 *    vazias, e a operacao que as buscas mais fazem ("quais sao os
 *    vizinhos desta casa?") fica em tempo constante com a grade.
 *    Etapa 1: aresta sem peso e nao direcionada (todo passo custa 1).
 *    Etapa 2: cada passagem vira DOIS arcos; o peso do arco u->v e o
 *    custo de ENTRAR em v (1 para livre/E/S, 3 para lama). Como o peso
 *    depende do sentido, o grafo e direcionado e isso e calculado por
 *    custo(lab[v]), sem matriz simetrica.
 *
 * e) Saida: caminho como sequencia (linha, coluna), contadas a partir de
 *    0 na matriz inteira (com a borda), da entrada ate a saida; numero
 *    de passos (casas - 1); na etapa 2 e na comparacao, o custo total
 *    (soma do custo de entrada de cada casa, sem contar a E). Sem
 *    caminho, a mensagem diz isso.
 *
 * Por que BFS na etapa 1: sem pesos, a fila processa as casas por
 * camadas de distancia; a primeira vez que uma casa e alcancada e pelo
 * menor numero de passos. Por que Dijkstra na etapa 2: com custos
 * diferentes e nenhum negativo, a casa de menor distancia ainda nao
 * definitiva ja tem distancia final, entao o relaxamento garante o menor
 * custo, mesmo que tenha mais passos que o caminho da largura.
 */
 
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define LINHAS 25
#define COLUNAS 71
#define N (LINHAS * COLUNAS)
#define INF 1000000000

// Labirinto: # parede, espaço caminho, ~ lama, E entrada e S saida
char lab[LINHAS][COLUNAS + 1] = {
    "#######################################################################",
    "#E  #                 #         #       #             ~       #       #",
    "###~# ### # ### ### # # ####### ##### ### ######### ##~## ### ####### #",
    "#       # #   # #   #   #        ~~ # ~ ~ #   #  ~  #  ~#   #~  #   # #",
    "# ### ###~### # # ##### # #### ####~##### ### # ##### # ### ### # # # #",
    "#   #~#   #   # #     # #   #~    #~~ # ~   ~   #     # ~ #   # ~ #   #",
    "### #~# ### ### ##### # ### # ### ### ### # ##### ####### # #~####### #",
    "# #   # #  ~  #   #   #     #   # #     # #         #       #     #   #",
    "# # # # ##### ##### ########### # #####~##### ####### ##### # #~# # ###",
    "# # # # #   #    ~#  ~          #     #     # # #     #       #~# ~   #",
    "# # # # # # ### # #####~#### ######## ##### # # # ##### ####### ##### #",
    "#   #  ~# # ~ # # #     #           # #   # #  ~#   # #  ~# #   #  ~ ~#",
    "# ### # # ### # #~# # # ##### ####### # ### # # ### # ### # # #~# #####",
    "#   # #   #~# #~#   # # #     #   ~ # # ~   # #  ~# # ~ # # # # #     #",
    "### # ##### # # ##### # # #####~### # #~##### # # # # ### # # ##### #~#",
    "# # ~       # #~    # #~  #   ~ # #       #     # # # #   # # #   # # #",
    "# # # ####### # ###~# ##### ## ## ####### ####### # #~# ###   # # #~#~#",
    "#   #  ~~ # ~ #   # # #   # #     #     #   #   # # #       #   # # # #",
    "#~### # # # ### # ### #~# # ### # # #~# ### ### # # #### ##~#####   # #",
    "#   # # #   # # #   #   #   #~ ~# # # #   # ~ # # #   #~  # #     # # #",
    "### # # ##### # ### ######### ### # # ####### #~#~### # # # #~##### # #",
    "# #~~ # #    ~  #~  ~     #  ~#     #     #       ~ #~  # # #   #   # #",
    "# # ###   ####### ###~##### # # ###### ## # ############# # ### # #####",
    "#      ~#           #    ~  #   ~    ~   ~   ~~           #   #  ~   S#",
    "#######################################################################"
};

// Movimentos: cima, direita, baixo e esquerda
int dl[4] = {-1, 0, 1, 0};
int dc[4] = {0, 1, 0, -1};

// Variaveis da busca em largura
int pai1[N], dist1[N], vis1[N], fila[N];

// Variaveis do Dijkstra
int pai2[N], dist2[N], def2[N];

// Define o custo de cada casa
int custo(char c)
{
    if (c == '~')
        return 3;

    return 1;
}

// Verifica se o labirinto esta correto
int valida(void)
{
    int i, j, ne = 0, ns = 0, ok = 1;
    char c;

    for (i = 0; i < LINHAS; i++) {
        for (j = 0; j < COLUNAS; j++) {
            c = lab[i][j];

            if (c == '\0') {
                printf("Linha %d curta: tem %d caracteres.\n", i, j);
                ok = 0;
                break;
            }

            if (c != ' ' && c != '~' && c != '#' && c != 'E' && c != 'S') {
                printf("Caractere invalido na posicao (%d, %d).\n", i, j);
                ok = 0;
            }

            if (c == 'E') ne++;
            if (c == 'S') ns++;
        }

        if (j == COLUNAS && lab[i][COLUNAS] != '\0') {
            printf("Linha %d comprida: mais de %d caracteres.\n", i, COLUNAS);
            ok = 0;
        }
    }

    if (ne != 1) {
        printf("Deve haver exatamente uma entrada E (ha %d).\n", ne);
        ok = 0;
    }

    if (ns != 1) {
        printf("Deve haver exatamente uma saida S (ha %d).\n", ns);
        ok = 0;
    }

    return ok;
}

// Localiza a entrada ou a saida no labirinto
int acha(char c)
{
    int i, j;

    for (i = 0; i < LINHAS; i++)
        for (j = 0; j < COLUNAS; j++)
            if (lab[i][j] == c)
                return i * COLUNAS + j;

    return -1;
}

// Encontra uma casa vizinha valida
int vizinho(int u, int k)
{
    int l = u / COLUNAS + dl[k];
    int c = u % COLUNAS + dc[k];

    if (l < 0 || l >= LINHAS || c < 0 || c >= COLUNAS)
        return -1;

    if (lab[l][c] == '#')
        return -1;

    return l * COLUNAS + c;
}

// Busca em largura: encontra o caminho com menos passos
void largura(int ini)
{
    int i, k, u, v, ini_f = 0, fim_f = 0;

    // Inicializa os vetores
    for (i = 0; i < N; i++) {
        pai1[i] = -1;
        dist1[i] = -1;
        vis1[i] = 0;
    }

    // Adiciona a entrada na fila
    vis1[ini] = 1;
    dist1[ini] = 0;
    fila[fim_f++] = ini;

    // Explora as casas enquanto houver elementos na fila
    while (ini_f < fim_f) {
        u = fila[ini_f++];

        for (k = 0; k < 4; k++) {
            v = vizinho(u, k);

            if (v != -1 && !vis1[v]) {
                vis1[v] = 1;
                dist1[v] = dist1[u] + 1;
                pai1[v] = u;
                fila[fim_f++] = v;
            }
        }
    }
}

// Dijkstra: encontra o caminho com menor custo
void dijkstra(int ini)
{
    int i, k, u, v, nd, melhor;

    // Inicializa os vetores
    for (i = 0; i < N; i++) {
        pai2[i] = -1;
        dist2[i] = INF;
        def2[i] = 0;
    }

    dist2[ini] = 0;

    while (1) {
        u = -1;
        melhor = INF;

        // Escolhe a casa nao definida com menor custo
        for (i = 0; i < N; i++)
            if (!def2[i] && dist2[i] < melhor) {
                melhor = dist2[i];
                u = i;
            }

        if (u == -1)
            break;

        def2[u] = 1;

        // Verifica os vizinhos da casa atual
        for (k = 0; k < 4; k++) {
            v = vizinho(u, k);

            if (v == -1 || def2[v])
                continue;

            // Calcula o custo para chegar ao vizinho
            nd = dist2[u] + custo(lab[v / COLUNAS][v % COLUNAS]);

            // Atualiza se encontrou um caminho mais barato
            if (nd < dist2[v]) {
                dist2[v] = nd;
                pai2[v] = u;
            }
        }
    }
}

// Reconstrói o caminho da entrada ate a saida
int monta(int pai[], int ini, int fim, int cam[])
{
    int n = 0, u, i, t;

    // Percorre os pais da saida ate a entrada
    for (u = fim; u != -1; u = pai[u])
        cam[n++] = u;

    // Inverte o caminho para ficar na ordem correta
    for (i = 0; i < n / 2; i++) {
        t = cam[i];
        cam[i] = cam[n - 1 - i];
        cam[n - 1 - i] = t;
    }

    if (cam[0] != ini)
        return 0;

    return n;
}

// Calcula o custo total do caminho
int soma(int cam[], int n)
{
    int i, s = 0;

    for (i = 1; i < n; i++)
        s += custo(lab[cam[i] / COLUNAS][cam[i] % COLUNAS]);

    return s;
}

// Mostra as coordenadas do caminho encontrado
void mostra(int cam[], int n)
{
    int i;

    for (i = 0; i < n; i++) {
        printf("(%d,%d)", cam[i] / COLUNAS, cam[i] % COLUNAS);

        if (i < n - 1)
            printf(" -> ");

        if ((i + 1) % 8 == 0)
            printf("\n");
    }

    printf("\n");
}

int main(void)
{
    int ent, sai, n1, n2, c1, c2, i, igual;
    int cam1[N], cam2[N];

    // Valida o labirinto antes de iniciar
    if (!valida()) {
        printf("Labirinto invalido. As buscas nao serao executadas.\n");
        return 1;
    }

    // Localiza a entrada e a saida
    ent = acha('E');
    sai = acha('S');

    // Executa os dois algoritmos
    largura(ent);
    dijkstra(ent);

    // Resultado da busca em largura
    printf("=== ETAPA 1: busca em largura (menos passos) ===\n");

    if (dist1[sai] == -1) {
        printf("Nao existe caminho da entrada ate a saida.\n");
    } else {
        n1 = monta(pai1, ent, sai, cam1);
        c1 = soma(cam1, n1);
        mostra(cam1, n1);

        printf("Passos: %d | Custo (com lama): %d\n", n1 - 1, c1);
    }

    // Resultado do Dijkstra
    printf("\n=== ETAPA 2: Dijkstra (menor custo) ===\n");

    if (dist2[sai] == INF) {
        printf("Nao existe caminho da entrada ate a saida.\n");
    } else {
        n2 = monta(pai2, ent, sai, cam2);
        c2 = soma(cam2, n2);
        mostra(cam2, n2);

        printf("Passos: %d | Custo total: %d\n", n2 - 1, c2);
    }

    // Compara os resultados dos dois algoritmos
    printf("\n=== COMPARACAO ===\n");

    if (dist1[sai] == -1 || dist2[sai] == INF) {
        printf("Saida inalcancavel: comparacao nao feita.\n");
        return 0;
    }

    printf("Largura : %d passos, custo %d\n", n1 - 1, c1);
    printf("Dijkstra: %d passos, custo %d\n", n2 - 1, c2);

    // Verifica se os caminhos possuem a mesma sequencia
    igual = (n1 == n2);

    for (i = 0; igual && i < n1; i++)
        if (cam1[i] != cam2[i])
            igual = 0;

    if (igual)
        printf("Os caminhos sao o mesmo (mesma sequencia de casas).\n");
    else if (c1 == c2)
        printf("Caminhos diferentes com o mesmo custo.\n");
    else
        printf("Caminhos diferentes: o de menos passos custa mais (%d contra %d).\n", c1, c2);

    return 0;
}
