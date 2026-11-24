-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffGradient
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffGradient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:11.994869+00:00
-- url     : https://prove2.me/theorems/ef631515-8b56-43fd-a1c6-9dbd5615b6ec
-- title:
--   St Cut Off Gradient
-- statement:
--   Definitions and structural lemmas for St Cut Off Gradient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCutOffGradient.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
def CutOffGradient.Statement : Prop :=
  ∃ K : ℝ, ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (k : ℕ)
    (y : Fin (d + 1) → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
        (vecCons (logLogCutAlong A P k) φ) y ≤ K / ((k : ℝ) + 1) * tubeDens J A P R φ y ∧
    chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
        (vecCons (fun x => logLogCutAlong A P k x ^ 2 / 2) φ) y ≤
      K / ((k : ℝ) + 1) * tubeDens J A P R φ y ∧
    chartAbsDens J A ((Metric.closedBall 0 R).indicator (logLogCutAlong A P k))
        (vecCons (logLogCutAlong A P k) φ) y ≤ K / ((k : ℝ) + 1) * tubeDens J A P R φ y
end
end GroundTheory.Heights₂.Heights


