-- Prove2me | Definitions.Def_PolicyGradTheory_ProjGA_Projection
-- name    : PolicyGradTheory_ProjGA_Projection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:55:42.370987+00:00
-- url     : https://prove2.me/theorems/a70b9015-ff37-4f6f-a7a5-b2ee835c545c
-- title:
--   Euclidean projection onto a set (P_{Δ(A)^{|S|}} of (9), p. 15; P_C of (55), p. 77)
-- statement:
--   Let $E$ be a normed space, $C\subseteq E$ a set and $P:E\to E$ a map. We say that $P$ is a **projection onto $C$** if, for every $z\in E$, the point $P(z)$ belongs to $C$ and is a point of $C$ nearest to $z$:
--   $$
--   P(z)\in C\quad\text{and}\quad \|z-P(z)\|\le\|z-y\|\quad\text{for all }y\in C.
--   $$
--   In a Euclidean space and for $C$ nonempty, closed and convex, the nearest point exists and is unique, so this property determines $P$ completely. It is the projection $P_{\Delta(\mathcal A)^{|\mathcal S|}}$ onto the product simplex in the projected gradient ascent update (9), and the projection $P_C$ in the gradient mapping (55) of Appendix E.
--
--   **Formalization Note** Mathlib has no projection map onto an arbitrary closed convex set, so statements take the projection as a function together with this characterizing predicate. The same notion is published as `SpectralProjGrad.Shared.IsProjOnto` on `EuclideanSpace ℝ (Fin n)`; this copy is generic in the space because the policies of this paper live on `EuclideanSpace ℝ (S × A)`.
-- source:
--   arXiv:1908.00261v5, §4.2, (9), p. 15; App. E, Definition E.1, (55), p. 77

import Mathlib

namespace PolicyGradTheory.ProjGA

/-- `Proj` is a Euclidean projection onto `C`: for every `z`, the point `Proj z` lies in `C` and is a
point of `C` nearest to `z` in the norm (the projection `P_{∆(A)^{|S|}}` of (9), arXiv:1908.00261v5,
§4.2, p. 15, and `P_C` of (55), App. E, p. 77). For a nonempty closed convex `C` in a Euclidean space
the nearest point exists and is unique, so the predicate determines `Proj`. -/
def IsProjOnto {E : Type*} [NormedAddCommGroup E] (C : Set E) (Proj : E → E) : Prop :=
  ∀ z : E, Proj z ∈ C ∧ ∀ y ∈ C, ‖z - Proj z‖ ≤ ‖z - y‖

end PolicyGradTheory.ProjGA


