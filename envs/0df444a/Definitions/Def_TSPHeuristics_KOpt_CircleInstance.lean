-- Prove2me | Definitions.Def_TSPHeuristics_KOpt_CircleInstance
-- name    : TSPHeuristics_KOpt_CircleInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:54:35.634345+00:00
-- url     : https://prove2.me/theorems/443c92a2-437b-4b12-b727-ae2a27ce1d33
-- title:
--   The circular-road instance $(N_n, d_n)$ of Theorem 5, its subtours $T_i$ and inserted nodes $a_i$
-- statement:
--   Place $n$ cities at equal spacing on a circular road. The paper's graph $(N_n,d_n)$ has nodes $N_n=\{1,\dots,n\}$ and
--   $$d_n(i,j)=\text{the smallest nonnegative integer } m \text{ with } i-j\equiv m \ \text{or}\ j-i\equiv m \pmod n,$$
--   the number of road segments between $i$ and $j$.
--
--   The subtours of the proof of Theorem 5 are $T_1=\{1\}$, $T_2=\{(1,2),(2,1)\}$ and, for $3\le i\le n$,
--   $$T_i=\{(1,2),(i-1,i)\}\cup\{(j,j+2): 1\le j\le i-2\}.$$
--   Read as a cycle, $T_i$ starts at $1$, runs through the even nodes $2,4,\dots$ up to $i$ in increasing order, and returns through the odd nodes of $(1,i]$ in decreasing order; for example $T_8=1,2,4,6,8,7,5,3$ (the paper's Fig. 4) and $T_7=1,2,4,6,7,5,3$. The inserted nodes are $a_i=i+1$ for $0\le i<n$.
--
--   This instance is the tight example for nearest and cheapest insertion (Theorem 5) and the example of a $k$-optimal tour with ratio $2(1-1/n)$ (Theorem 6).
--
--   **Formalization Note** Nodes are 0-based: the paper's node $m$ is `⟨m - 1, _⟩ : Fin n`, so $d_n$ becomes `cycDist n`, computed with natural-number residues $(i+n-j) \bmod n$ (no truncated subtraction occurs because $j<n$), and $a_i=i+1$ becomes the index $i$ (`circleNode`, reduced mod $n$ only to make it total; it takes a proof of $0<n$). `circleSubtour n i` is the list form of $T_i$ with the paper's 1-based index $i$; `circleSubtour n 0` is the empty list and is never used.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 575, proof of Theorem 5 (definition of (N_n, d_n)) and Fig. 4; p. 576, definitions of T_i and a_i

import Mathlib

namespace TSPHeuristics.KOpt

/-- The distance of the graph `(N_n, d_n)` in the proof of Theorem 5 (p. 575): "d_n(i, j) =
smallest nonnegative integer m such that i − j ≡ m (mod n) or j − i ≡ m (mod n)", i.e. the
distance between `i` and `j` along a cycle of `n` equally spaced nodes. The paper's node `m`
(`1 ≤ m ≤ n`) is `⟨m - 1, _⟩ : Fin n`; the shift does not change any difference mod `n`. -/
def cycDist (n : ℕ) (i j : Fin n) : ℝ :=
  ((min ((i.val + n - j.val) % n) ((j.val + n - i.val) % n) : ℕ) : ℝ)

/-- The subtours `T_i` of the proof of Theorem 5 (p. 576), with the paper's 1-based index `i`:
"T_1 [is] the tour on set {1}, … T_2 = {(1, 2), (2, 1)} and for 3 ≦ i ≦ n …
T_i = {(1, 2), (i − 1, i)} ∪ {(j, j + 2) | 1 ≦ j ≦ i − 2}."
As a closed list (0-based nodes, paper node `m` is `m - 1`), `T_i` visits the paper's node 1, then
the even nodes `2, 4, …` up to `i` in increasing order, then the odd nodes in `(1, i]` in decreasing
order, and returns to 1: `T_8 = 1, 2, 4, 6, 8, 7, 5, 3` (Fig. 4), `T_7 = 1, 2, 4, 6, 7, 5, 3`,
`T_3 = 1, 2, 3`, `T_2 = 1, 2`, `T_1 = 1`. Its edges are exactly the paper's edge set. -/
def circleSubtour (n i : ℕ) : List (Fin n) :=
  (List.finRange n).filter (fun m => m.val < i ∧ m.val = 0) ++
    (List.finRange n).filter (fun m => m.val < i ∧ Odd m.val) ++
    ((List.finRange n).filter (fun m => m.val < i ∧ m.val ≠ 0 ∧ Even m.val)).reverse

/-- The inserted nodes of the proof of Theorem 5 (p. 576): "a_i = i + 1 for 0 ≦ i < n". With
0-based nodes the paper's node `i + 1` is `⟨i, _⟩`, so `circleNode n hn i = ⟨i, _⟩` for `i < n`
(the reduction mod `n` only makes the function total). -/
def circleNode (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n :=
  ⟨i % n, Nat.mod_lt i hn⟩

end TSPHeuristics.KOpt


