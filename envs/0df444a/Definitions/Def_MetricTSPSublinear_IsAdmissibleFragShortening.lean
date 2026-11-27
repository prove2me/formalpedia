-- Prove2me | Definitions.Def_MetricTSPSublinear_IsAdmissibleFragShortening
-- name    : MetricTSPSublinear_IsAdmissibleFragShortening
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T05:33:33.654873+00:00
-- url     : https://prove2.me/theorems/fc6e4dc8-dddc-4165-aab6-852fc4129117
-- title:
--   Admissible shortening of a cell fragment (constraints (10))
-- statement:
--   Let $d$ be a metric on $V$, $E$ the edge set of a spanning tree $T$ (the MST), $F\subseteq V$ a cell fragment with root $o_F$, and $\lambda,r>0$. A function $t$ on pairs is an **admissible shortening** of $F$ if it vanishes off the edges of $T$ inside $F$ (`insideEdges E F`), satisfies $0\le t(e)\le d(e)$ on the edges of $T$, and the tree distances $d_t$ along $T$ obey the constraints (10):
--   $$d_t(u,v)\le d(u,v)\ \ (u,v\in F),\qquad d_t(v,o_F)\le d(v,x)\ \ (v\in F,\ x\notin F),\qquad d_t(v,o_F)\le\lambda r\ \ (v\in F).$$
--   The first condition is domination by the metric, the second bounds the depth of a vertex by its distance to any vertex outside the fragment, and the third bounds the depth. The local weight $A_P$ of a contracted cell is the sum over its cell fragments of the maximum weight of an admissible shortening.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §7.1.2, constraints (10), p.23 (PDF p.25).

import Mathlib
import Definitions.Def_DoublingMST_edgeCost
import Definitions.Def_MetricTSPSublinear_treeDist

open scoped Classical

namespace MetricTSPSublinear

/-- The edges of `E` with both endpoints in `F`. -/
def insideEdges {n : ℕ} (E : Finset (Sym2 (Fin n))) (F : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  E.filter (fun e => ∀ z ∈ e, z ∈ F)

/-- **An admissible shortening of a cell fragment** (constraints (10)). Azarmehr, Behnezhad, *Metric TSP in Sublinear
Time: Breaking Two Approximation*, arXiv:2611.04283, §7.1.2, p.23 (PDF p.25): a shortening `t_F` of the fragment `F`
(weights between `0` and the MST weight on the edges inside `F`) with
`d_{t_F}(u,v) ≤ d(u,v)` (u,v ∈ F), `d_{t_F}(v,o_F) ≤ d(v,x)` (v ∈ F, x ∉ F), `d_{t_F}(v,o_F) ≤ λr` (v ∈ F). -/
def IsAdmissibleFragShortening {n : ℕ} (d : Fin n → Fin n → ℝ) (E : Finset (Sym2 (Fin n)))
    (F : Finset (Fin n)) (o : Fin n) (lam r : ℝ) (t : Sym2 (Fin n) → ℝ) : Prop :=
  (∀ e, e ∉ insideEdges E F → t e = 0) ∧
  (∀ e ∈ E, 0 ≤ t e ∧ t e ≤ DoublingMST.edgeCost d e) ∧
  (∀ u ∈ F, ∀ v ∈ F, treeDist E t u v ≤ d u v) ∧
  (∀ v ∈ F, ∀ x ∉ F, treeDist E t v o ≤ d v x) ∧
  (∀ v ∈ F, treeDist E t v o ≤ lam * r)

end MetricTSPSublinear


