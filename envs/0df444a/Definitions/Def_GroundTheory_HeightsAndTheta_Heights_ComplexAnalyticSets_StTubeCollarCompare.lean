-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeCollarCompare
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeCollarCompare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:24.274684+00:00
-- url     : https://prove2.me/theorems/3fddfa3b-b4c3-433a-9cb7-6f968bf7ae54
-- title:
--   St Tube Collar Compare
-- statement:
--   Definitions and structural lemmas for St Tube Collar Compare, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTubeCollarCompare.lean

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
def TubeCollarCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      ∃ C : ℝ, ∀ y, {y | -Real.exp 1 ≤ logAbsSq P y}.indicator (tubeDens J A P R (fun _ => euclPot)) y ≤
        C * chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ))
          (fun _ : Fin (d + 1) => euclPot) y
end
end GroundTheory.Heights₂.Heights


