-- Prove2me | Definitions.Def_IntervalToDynamic_LossClass
-- name    : IntervalToDynamic_LossClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:39.551098+00:00
-- url     : https://prove2.me/theorems/7530443a-375d-47ed-80c1-054f8d5ee042
-- title:
--   The class of losses on $\mathcal Y$ the inner algorithm must handle
-- statement:
--   Let $\mathcal Y=\mathcal B(D_{\mathcal X})$. A function $h$ belongs to the class of the selected mode when $h$ is differentiable and convex on $\mathcal Y$, $G_h$-Lipschitz on $\mathcal Y$, and in the exp-concave mode $\alpha_h$-exp-concave on $\mathcal Y$, in the strongly convex mode $\lambda$-strongly convex on $\mathcal Y$, with $G_h,\alpha_h$ from Table 2.
--
--   This is the class on which Theorem 4 asks for an interval regret guarantee.
--
--   **Formalization Note** Mathlib's `StrongConvexOn Y lam h` has modulus $\frac{\lambda}2r^2$, the usual $\lambda$-strong convexity. Smoothness is not part of the class: Table 2 uses $H_h$ only in hindsight.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 4, p.8; Table 2, p.9

import Mathlib
import Definitions.Def_IntervalToDynamic_Gh
import Definitions.Def_IntervalToDynamic_alphaH
import Definitions.Def_LogRegretOCO_ONS_IsExpConcaveOn

namespace IntervalToDynamic

/-- The class of losses on `Y = B(D_X)` which the inner algorithm `A` must handle. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Theorem 4,
p.8 ("for convex, exp-concave, or strongly convex losses"), with the parameters of the right column
of Table 2, p.9: `h` is differentiable and convex on `Y` and `G_h`-Lipschitz on `Y`, and in the
curved regimes `α_h`-exp-concave on `Y`, respectively `λ`-strongly convex on `Y`.

**Formalization Note.** Mathlib's `StrongConvexOn Y lam h` has modulus `(lam/2) r²`, the usual
`lam`-strong convexity. Smoothness is not part of the class: Table 2 says `H_h` is used "only in
hindsight analysis". -/
def LossClass {d : ℕ} (mode : LossMode) (DX G : ℝ) (h : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  DifferentiableOn ℝ h (Metric.closedBall 0 DX) ∧
  ConvexOn ℝ (Metric.closedBall 0 DX) h ∧
  (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) DX, ∀ y' ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) DX,
    |h y - h y'| ≤ Gh mode DX G * ‖y - y'‖) ∧
  match mode with
  | .convex => True
  | .expConcave α => LogRegretOCO.ONS.IsExpConcaveOn (alphaH DX G α) (Metric.closedBall 0 DX) h
  | .stronglyConvex lam => StrongConvexOn (Metric.closedBall 0 DX) lam h

end IntervalToDynamic


