-- Prove2me | Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily
-- name    : TSPHeuristics_NNLower_LowerBoundFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:23:49.151992+00:00
-- url     : https://prove2.me/theorems/c256ea0b-3354-452d-866a-1b27c3b1ac77
-- title:
--   The graphs $F_i$, $G_i$, $\bar G_i$, the paths $P_i$, and the numbers $l_i$, $L_i$ of Theorem 2
-- statement:
--   These are the objects of the proof of Theorem 2 (pp. 567–568, Figs. 1–2).
--
--   1. **The lengths** $l_i$, eq. (2.11):
--   $$l_i=\tfrac16\bigl(4\cdot 2^i-(-1)^i+3\bigr),$$
--   so $l_1=2$, $l_2=3$, $l_3=6$, $l_4=11$.
--   2. **The graph** $F_i$ ($i\ge1$) is an incomplete weighted graph with $n_i=2^{i+1}-1$ nodes and three distinguished nodes: the start node, the middle node and the right node. $F_1$ is a triangle with all three edges of weight $1$ (start $0$, middle $1$, right $2$). $F_{i+1}$ consists of a left copy and a right copy of $F_i$ and one new node $D$, which becomes the middle node. With the labels of Fig. 1 ($A$ start, $B$ middle, $C$ right of the left copy; $E$ start, $F$ middle, $G$ right of the right copy), the new edges are $(C,D)$ and $(D,E)$ of length $1$, and $(D,F)$ and $(B,E)$ of length $l_i$. The start node of $F_{i+1}$ is $A$ and its right node is $G$.
--   3. **The path** $P_i$ goes from the start node to the middle node of $F_i$ and visits every node: $P_1$ is start, right, middle; $P_{i+1}$ is $P_i$ in the left copy, the edge $(B,E)$, $P_i$ in the right copy, and the edge $(F,D)$.
--   4. **The length** $L_i$ of $P_i$ satisfies $L_1=2$ and $L_{i+1}=2L_i+2l_i$ (p. 567).
--   5. **The graph** $G_i$ is $F_i$ plus an edge of length $1$ between the start and the right node and an edge of length $l_i-1$ between the middle node and the start node.
--   6. **The complete graph** $\bar G_i$ has the nodes of $G_i$, and $d(a,b)$ is the length of a minimal path from $a$ to $b$ in $G_i$.
--
--   Throughout, the nodes of $F_i$, $G_i$ and $\bar G_i$ are numbered $0,1,\dots,n_i-1$ from left to right, where $n_i = 2^{i+1}-1$; the start node is $0$, the middle node is $2^i-1$ and the right node is $n_i-1$. In $F_{i+1}$ the left copy of $F_i$ occupies $0,\dots,n_i-1$, the new node $D$ is $n_i$, and the right copy occupies $n_i+1,\dots,2n_i$.
--
--   **Formalization Note** Graphs are lists of edges $(a,b,w)$ with real weights; $\bar G_i$'s distance is the shortest-path distance of `ShortestPathMetric`. $l_i$ is defined in $\mathbb R$ exactly as printed. $L_i$ is defined by the paper's difference equation; that it is also the length of the tour along $P_i$ in $\bar G_i$ (minus $l_i-1$) is a milestone. The index $i=0$ is not used by the paper; the definitions give it placeholder values ($F_0$ has no edges, $P_0$ is empty, $L_0=0$) and every statement assumes $i\ge1$.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 567, proof of Theorem 2, Fig. 1, eq. (2.11) and the difference equation for L_i; p. 568, definitions of G_i and Ḡ_i, Fig. 2

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_ShortestPathMetric

namespace TSPHeuristics.NNLower

/-- The edge length `l_i` of eq. (2.11), p. 567: `l_i = (1/6)(4 · 2^i − (−1)^i + 3)`. -/
noncomputable def ell (i : ℕ) : ℝ := (4 * 2 ^ i - (-1) ^ i + 3) / 6

/-- The number of nodes of `F_i` (and of `G_i`, `Ḡ_i`): `2^(i+1) − 1`. -/
def numNodes (i : ℕ) : ℕ := 2 ^ (i + 1) - 1

/-- The position of the middle node of `F_i`: `2^i − 1`. The start node is `0` and the right
node is `numNodes i − 1`; the nodes of `F_i` are `0, 1, …, numNodes i − 1`, left to right. -/
def middle (i : ℕ) : ℕ := 2 ^ i - 1

/-- The edges of the incomplete weighted graph `F_i` (pp. 567, Fig. 1), for `i ≥ 1`, as triples
(endpoint, endpoint, weight). `F_1` is a triangle with all weights `1`. `F_{i+1}` consists of the
left copy of `F_i` (nodes `0 … s − 1`, `s = numNodes i`), the new node `D = s`, and the right copy
of `F_i` shifted by `s + 1`, plus the edges `(C, D)` and `(D, E)` of length `1`, `(D, F)` and
`(B, E)` of length `l_i`, where `B = middle i`, `C = s − 1`, `E = s + 1`, `F = s + 1 + middle i`.
The value at `i = 0` is a placeholder (`F_0` is not defined in the paper). -/
noncomputable def edgesF : ℕ → List (ℕ × ℕ × ℝ)
  | 0 => []
  | 1 => [(0, 1, 1), (1, 2, 1), (0, 2, 1)]
  | i + 2 =>
    edgesF (i + 1) ++
      (edgesF (i + 1)).map (fun e => (e.1 + (numNodes (i + 1) + 1), e.2.1 + (numNodes (i + 1) + 1), e.2.2)) ++
      [(numNodes (i + 1) - 1, numNodes (i + 1), 1),
       (numNodes (i + 1), numNodes (i + 1) + 1, 1),
       (numNodes (i + 1), numNodes (i + 1) + 1 + middle (i + 1), ell (i + 1)),
       (middle (i + 1), numNodes (i + 1) + 1, ell (i + 1))]

/-- The path `P_i` of `F_i` (p. 567), as the list of nodes it visits from the start node to the
middle node: `P_1 = [start, right, middle] = [0, 2, 1]`; `P_{i+1}` is `P_i` in the left copy, the
edge `(B, E)`, `P_i` in the right copy, and the edge `(F, D)`. -/
def pathP : ℕ → List ℕ
  | 0 => []
  | 1 => [0, 2, 1]
  | i + 2 => pathP (i + 1) ++ (pathP (i + 1)).map (· + (numNodes (i + 1) + 1)) ++ [numNodes (i + 1)]

/-- The length `L_i` of the path `P_i`, given by the difference equation of p. 567:
`L_1 = 2`, `L_{i+1} = 2 · L_i + 2 · l_i`. The value at `i = 0` is a placeholder. -/
noncomputable def pathLength : ℕ → ℝ
  | 0 => 0
  | 1 => 2
  | i + 2 => 2 * pathLength (i + 1) + 2 * ell (i + 1)

/-- The edges of `G_i` (p. 568): the edges of `F_i` plus an edge of length `1` between the start
node and the right node and an edge of length `l_i − 1` between the middle node and the start
node. -/
noncomputable def edgesG (i : ℕ) : List (ℕ × ℕ × ℝ) :=
  edgesF i ++ [(0, numNodes i - 1, 1), (middle i, 0, ell i - 1)]

/-- The complete graph `Ḡ_i` (p. 568) on the nodes of `G_i`: `d(a, b)` is the length of a minimal
path from `a` to `b` in `G_i`. -/
noncomputable def gbar (i : ℕ) : Fin (numNodes i) → Fin (numNodes i) → ℝ :=
  fun a b => spDist (edgesG i) a b

end TSPHeuristics.NNLower


