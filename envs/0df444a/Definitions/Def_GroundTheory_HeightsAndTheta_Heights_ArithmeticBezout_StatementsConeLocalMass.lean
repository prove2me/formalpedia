-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:58.764882+00:00
-- url     : https://prove2.me/theorems/51649e5e-00be-49d3-b629-63150de295c8
-- title:
--   Statements Cone Local Mass
-- statement:
--   Definitions and structural lemmas for Statements Cone Local Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeLocalMass.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
def ConeLocalMass.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
      ∀ R : ℝ, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J ∩ Metric.ball 0 R) < ⊤
end
end GroundTheory.Heights₂.Heights


