-- Prove2me | Definitions.Def_IntervalToDynamic_Supplement_FixedKWrapper
-- name    : IntervalToDynamic_Supplement_FixedKWrapper
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:36:53.498313+00:00
-- url     : https://prove2.me/theorems/80f0e6a6-36a9-4533-85ca-37084f73b941
-- title:
--   Algorithm 1 on $\mathcal Y=B(\kappa_kD_{\mathcal X})$ with recomputed surrogate parameters
-- statement:
--   For fixed $k\ge1$, set $\kappa_1=1$, $\kappa_k=6(k-1)$ for $k\ge2$, and
--   $$
--   \mathcal Y=B(\kappa_kD_{\mathcal X}),\qquad D_{\mathcal Y}=2\kappa_kD_{\mathcal X}.
--   $$
--   The wrapper recomputes Eq. (14) and every Table 2 coefficient with this $D_{\mathcal Y}$, forms the corrected gradient after projecting the inner decision onto $\mathcal X$, feeds the appropriate convex, exp-concave or strongly convex surrogate to the history-based inner algorithm, and records the inner decisions $y_t$, proper projections $x_t$, and surrogate losses $h_t$.
--
--   The corresponding loss class consists of differentiable convex losses on $\mathcal Y$ with the recomputed Lipschitz coefficient $G_h$ and, in the curved modes, the recomputed exp-concavity coefficient $\alpha_h$ or the printed strong-convexity coefficient $\lambda$.
--
--   **Formalization Note** This is a new fixed-$k$ wrapper rather than the published $k=1$ wrapper: reusing the latter would silently set $D_{\mathcal Y}=2D_{\mathcal X}$.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Eq. (17), p.12; Eq. (14) and Table 2, p.9; Appendix B.5, pp.33–39

import Mathlib
import Definitions.Def_IntervalToDynamic_LossMode
import Definitions.Def_IntervalToDynamic_OnlineAlgorithm
import Definitions.Def_IntervalToDynamic_proj
import Definitions.Def_IntervalToDynamic_correctedGrad
import Definitions.Def_LogRegretOCO_ONS_IsExpConcaveOn

namespace IntervalToDynamic.Supplement

/-- The expansion factor of Eq. (17): `κ₁ = 1`, `κ_k = 6(k-1)` for `k ≥ 2`. -/
def kappa (k : ℕ) : ℝ := if k = 1 then 1 else 6 * (k - 1)

/-- The diameter parameter `D_Y = 2 κ_k D_X` of Eq. (17). -/
def diameterY (k : ℕ) (DX : ℝ) : ℝ := 2 * kappa k * DX

/-- Eq. (14), recomputed with `D_Y = 2 κ_k D_X`. -/
noncomputable def gammaK (k : ℕ) (DX G alpha : ℝ) : ℝ :=
  (1 / 2) * min alpha (min (1 / (DX * G)) (4 / ((DX + diameterY k DX) * G)))

/-- Table 2's surrogate Lipschitz coefficient, recomputed for Eq. (17). -/
noncomputable def GhK (k : ℕ) (mode : IntervalToDynamic.LossMode) (DX G : ℝ) : ℝ :=
  match mode with
  | .convex => G
  | .expConcave alpha => (1 + gammaK k DX G alpha * diameterY k DX * G) * G
  | .stronglyConvex lam => G + lam * (DX + diameterY k DX) / 2

/-- Table 2's exp-concavity coefficient on the enlarged domain of Eq. (17). -/
noncomputable def alphaHK (k : ℕ) (DX G alpha : ℝ) : ℝ :=
  gammaK k DX G alpha / (1 + gammaK k DX G alpha * diameterY k DX * G) ^ 2

/-- Table 2's hindsight smoothness coefficient. -/
noncomputable def HhK (k : ℕ) (mode : IntervalToDynamic.LossMode) (DX G : ℝ) : ℝ :=
  2 * GhK k mode DX G / DX

/-- The surrogate loss class on `Y = B(κ_k D_X)` with every Table 2 coefficient recomputed
using `D_Y = 2 κ_k D_X`. -/
def LossClassK {d : ℕ} (k : ℕ) (mode : IntervalToDynamic.LossMode) (DX G : ℝ)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  let Y : Set (EuclideanSpace ℝ (Fin d)) := Metric.closedBall 0 (kappa k * DX)
  DifferentiableOn ℝ h Y ∧ ConvexOn ℝ Y h ∧
  (∀ y ∈ Y, ∀ y' ∈ Y, |h y - h y'| ≤ GhK k mode DX G * ‖y - y'‖) ∧
  match mode with
  | .convex => True
  | .expConcave alpha => LogRegretOCO.ONS.IsExpConcaveOn (alphaHK k DX G alpha) Y h
  | .stronglyConvex lam => StrongConvexOn Y lam h

/-- Eqs. (10)--(12) with Eq. (14) recomputed for the fixed-`k` domain. -/
noncomputable def surrogateK {d : ℕ} (k : ℕ) (mode : IntervalToDynamic.LossMode) (DX G : ℝ)
    (dv x y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) → ℝ :=
  match mode with
  | .convex => fun y' => inner ℝ dv y'
  | .expConcave alpha => fun y' =>
      inner ℝ dv y' + (gammaK k DX G alpha / 2) * (inner ℝ dv (y' - y)) ^ 2
  | .stronglyConvex lam => fun y' => inner ℝ dv y' + (lam / 2) * ‖y' - x‖ ^ 2

noncomputable def fixedKRoundLoss {d : ℕ} (k : ℕ) (mode : IntervalToDynamic.LossMode)
    (X : Set (EuclideanSpace ℝ (Fin d))) (DX G : ℝ)
    (gr : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) → ℝ :=
  let x := IntervalToDynamic.proj X y
  surrogateK k mode DX G (IntervalToDynamic.correctedGrad (gr x) (y - x)) x y

/-- Algorithm 1's adaptive loss history with the fixed-`k` parameters of Eq. (17). -/
noncomputable def fixedKHistory {d : ℕ} (k : ℕ) (mode : IntervalToDynamic.LossMode)
    (X : Set (EuclideanSpace ℝ (Fin d))) (DX G : ℝ)
    (A : IntervalToDynamic.OnlineAlgorithm (EuclideanSpace ℝ (Fin d)))
    (g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    ℕ → List (EuclideanSpace ℝ (Fin d) → ℝ)
  | 0 => []
  | n + 1 => fixedKHistory k mode X DX G A g n ++
      [fixedKRoundLoss k mode X DX G (g (n + 1))
        (A (fixedKHistory k mode X DX G A g n))]

/-- The three sequences of the fixed-`k` wrapper: inner decisions `y_t`, proper projections `x_t`,
and adaptive surrogate losses `h_t`. -/
structure FixedKWrapper (E : Type*) where
  y : ℕ → E
  x : ℕ → E
  h : ℕ → E → ℝ

noncomputable def fixedKWrapper {d : ℕ} (k : ℕ) (mode : IntervalToDynamic.LossMode)
    (X : Set (EuclideanSpace ℝ (Fin d))) (DX G : ℝ)
    (A : IntervalToDynamic.OnlineAlgorithm (EuclideanSpace ℝ (Fin d)))
    (g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    FixedKWrapper (EuclideanSpace ℝ (Fin d)) :=
  { y := fun t => A (fixedKHistory k mode X DX G A g (t - 1))
    x := fun t => IntervalToDynamic.proj X
      (A (fixedKHistory k mode X DX G A g (t - 1)))
    h := fun t => fixedKRoundLoss k mode X DX G (g t)
      (A (fixedKHistory k mode X DX G A g (t - 1))) }

end IntervalToDynamic.Supplement


