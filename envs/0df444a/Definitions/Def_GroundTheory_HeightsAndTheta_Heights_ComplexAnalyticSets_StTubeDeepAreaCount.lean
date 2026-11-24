-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepAreaCount
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepAreaCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:16.038473+00:00
-- url     : https://prove2.me/theorems/74e3d97f-e711-4c8d-b390-d44a6260bfd0
-- title:
--   St Tube Deep Area Count
-- statement:
--   Definitions and structural lemmas for St Tube Deep Area Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTubeDeepAreaCount.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepRankOne
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
open scoped ENNReal
noncomputable section
def TubeDeepAreaCount.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
      ∃ N : ℕ, ∀ g : (Fin (d + 1) → ℂ) → ℝ, Measurable g → (∀ z, 0 ≤ g z) →
        ∫⁻ y, ENNReal.ofReal (sheetSum J A (fun x s =>
            (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
              ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y) ≤
          (N : ℝ≥0∞) * ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R}, ENNReal.ofReal (g z)
end
end GroundTheory.Heights₂.Heights


