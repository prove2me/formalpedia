-- Prove2me | Definitions.Def_TSPHeuristics_KOpt_UnitEdgeCount
-- name    : TSPHeuristics_KOpt_UnitEdgeCount
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:54:56.270197+00:00
-- url     : https://prove2.me/theorems/a7326d41-56ef-4af1-8fdc-e84db8f5c37f
-- title:
--   Unit edges $E_n$ of the circle and COUNT(e, T)
-- statement:
--   In the circle graph $(N_n,d_n)$ the edges of length one are
--   $$E_n=\{(1,n)\}\cup\{(i,i+1): 1\le i<n\}.$$
--   Every tour edge $(x,y)$ can be replaced by a path in $E_n$ of length $d_n(x,y)$: an arc of the circle between $x$ and $y$. Doing this for every edge of a tour $T$ gives a closed circuit $\alpha(T)$ of the same length, and **COUNT(e, T)** is the number of times the unit edge $e\in E_n$ occurs in $\alpha(T)$.
--
--   The arc is fixed canonically: the shorter of the two arcs between $x$ and $y$, and, when both have length $n/2$, the arc through $\min(x,y),\min(x,y)+1,\dots,\max(x,y)$.
--
--   COUNT turns tour lengths on the circle into sums of unit-edge counts and underlies the parity argument of Theorem 6.
--
--   **Formalization Note** Nodes are 0-based and the unit edge with index $e$ joins $e$ and $e+1 \bmod n$: index $i-1$ is the paper's $(i,i+1)$ and index $n-1$ is the paper's $(1,n)$. The paper replaces each tour edge "by a path of equal length from $E_n$" without saying which path in the antipodal case; the choice made here only makes COUNT a function, and the paper's argument holds for any choice. `unitCount τ e` counts the positions $k$ of the tour whose edge $(\tau(k),\tau(k+1))$ has an arc through $e$.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 580, proof of Theorem 6 (definitions of E_n, α(T), COUNT(e, T))

import Mathlib

namespace TSPHeuristics.KOpt

/-- The unit edges `E_n` of the circle graph (p. 580): "E_n = {(1, n)} ∪ {(i, i + 1) for 1 ≦ i < n}".
With 0-based nodes the unit edge with index `e : Fin n` joins `e` and `e + 1 (mod n)`: index
`e = i - 1` is the paper's `(i, i + 1)` for `1 ≤ i < n`, and index `n - 1` is the paper's `(1, n)`.

`arcCovers n x y e` says that the unit edge `e` lies on the canonical path in `E_n` that replaces the
tour edge `(x, y)`: the shorter of the two arcs of the circle between `x` and `y`, and when the two
arcs have equal length (`n` even, `x`, `y` antipodal) the arc through the nodes
`min x y, min x y + 1, …, max x y`. The arc has `d_n(x, y)` unit edges. The paper replaces "each
edge of T by a path of equal length from E_n" without fixing the path in the tied case; this fixes
one choice so that COUNT is a function. -/
def arcCovers (n : ℕ) (x y e : Fin n) : Prop :=
  if 2 * (max x.val y.val - min x.val y.val) ≤ n then
    min x.val y.val ≤ e.val ∧ e.val < max x.val y.val
  else
    e.val < min x.val y.val ∨ max x.val y.val ≤ e.val

instance (n : ℕ) (x y e : Fin n) : Decidable (arcCovers n x y e) := by
  unfold arcCovers; infer_instance

/-- COUNT(e, T) (p. 580): the number of times the unit edge `e` occurs in the circuit α(τ) obtained
by replacing each edge `(τ k, τ (k + 1))` of the tour `τ` by its canonical arc (`arcCovers`). -/
def unitCount {n : ℕ} (τ : Equiv.Perm (Fin n)) (e : Fin n) : ℕ :=
  (Finset.univ.filter (fun k : Fin n => arcCovers n (τ k) (τ (finRotate n k)) e)).card

end TSPHeuristics.KOpt


