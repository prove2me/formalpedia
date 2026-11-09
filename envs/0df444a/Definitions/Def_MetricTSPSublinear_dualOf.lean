-- Prove2me | Definitions.Def_MetricTSPSublinear_dualOf
-- name    : MetricTSPSublinear_dualOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:26:25.350943+00:00
-- url     : https://prove2.me/theorems/5eef9ee9-def5-4416-8d3e-6c1c29fb9882
-- title:
--   The dual solution of a Steiner tree
-- statement:
--   Let $F$ be a Steiner tree on $S$ and fix a point $x_0\in S$. The **dual solution of $F$** starts with $y_A=0$ for all $A$; for every edge $e$ of $F$, let $A$ be the set of points of $S$ lying in the component of $F\setminus e$ that does not contain $x_0$, and add $w_F(e)$ to $y_A$.
--
--   The cuts separating two points $u,v$ with positive $y$-value are exactly those of the edges on the $u$–$v$ path of $F$.
--
--   **Formalization Note.** The paper says "one of the two connected components"; the component away from a fixed point $x_0$ is the convention of the proof of Lemma 4.2. Since $\delta(A)=\delta(S\setminus A)$, the choice does not affect which pairs a cut separates.
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §4.1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MetricTSPSublinear_SteinerTree

open scoped Classical

namespace MetricTSPSublinear

/-- The side of an edge `e` of `F` away from `x₀`: the points `v ∈ S` whose node is not reachable from `ι x₀` in
`F \ e`. -/
noncomputable def SteinerTree.side {n : ℕ} {S : Finset (Fin n)} (F : SteinerTree S) (e : Sym2 (Fin F.m))
    (x₀ : Fin n) : Finset (Fin n) :=
  S.filter (fun v => ¬ (F.T.G.deleteEdges {e}).Reachable (F.ι x₀) (F.ι v))

/-- **The dual solution of a Steiner tree.**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §4.1, p.12 (PDF p.14): "Such a tree F naturally corresponds to a dual solution: Start with y_A = 0
for all A. For any edge e ∈ F, let A denote the vertices of V lying in one of the two connected components of F \ e.
Considering edge e, add w_F(e) to y_A."

`dualOf F x₀ A` is the sum of `w_F(e)` over the edges `e` of `F` whose side `F.side e x₀` equals `A`.

**Formalization Note.** The page leaves open which of the two components gives `A`. This definition takes the
component not containing the node of a fixed point `x₀` (the convention of the proof of Lemma 4.2, "x ∉ A"). Since
`δ(A) = δ(S \ A)`, the choice does not affect which pairs a cut separates. -/
noncomputable def dualOf {n : ℕ} {S : Finset (Fin n)} (F : SteinerTree S) (x₀ : Fin n) :
    Finset (Fin n) → ℝ :=
  fun A => ∑ e ∈ F.edges, if F.side e x₀ = A then F.T.w e else 0

end MetricTSPSublinear


