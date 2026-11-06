-- Prove2me | Definitions.Def_MatchedUCLB_baseNB
-- name    : MatchedUCLB_baseNB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:50.607166+00:00
-- url     : https://prove2.me/theorems/86edd732-88a5-477d-9016-49ca74a617d8
-- title:
--   The replacement formula $N^B_j$
-- statement:
--   With the notation of the partial bases, the **replacement formula** at the next center $c_{j+1}$ is
--
--   $$
--   N^B_j(x)=B_j(c_{j+1})+C_j+\langle\nabla B_j(c_{j+1}),x-c_{j+1}\rangle+\frac{\mu}{q}\|x-c_{j+1}\|^q,\qquad C_j=a_{\mathrm{lift}}\mu\theta^2R_j^q .
--   $$
--
--   It keeps the endpoint gradient of $B_j$, raises the value by $C_j$, and adds the Euclidean $q$th power centered at $c_{j+1}$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.3), p.6; Eq. (4.6), p.6

import Mathlib
import Definitions.Def_MatchedUCLB_baseSeq

namespace MatchedUCLB

/-- **The replacement formula `N^B_j`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.3), p.6:
"`N^B_j(x) = B_j(c_{j+1}) + C_j + ⟨∇B_j(c_{j+1}), x − c_{j+1}⟩ + (μ/q)‖x − c_{j+1}‖^q`", with
`C_j = a_lift μ θ² R_j^q`, `R_j = ‖h_j‖` (4.6).

**Formalization Note.** This is the second argument of the smooth maximum in `baseSeq`. -/
noncomputable def baseNB (q μ : ℝ) {d : ℕ} (h : ℕ → EuclideanSpace ℝ (Fin d)) (j : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  baseSeq q μ h j (center h (j + 1)) + aLift q * μ * theta q ^ 2 * ‖h j‖ ^ q +
    fderiv ℝ (baseSeq q μ h j) (center h (j + 1)) (x - center h (j + 1)) +
    μ / q * ‖x - center h (j + 1)‖ ^ q

end MatchedUCLB


