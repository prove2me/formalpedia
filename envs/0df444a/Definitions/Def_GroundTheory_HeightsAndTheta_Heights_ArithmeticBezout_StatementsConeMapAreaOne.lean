-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapAreaOne
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapAreaOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:39.936141+00:00
-- url     : https://prove2.me/theorems/4f1923a4-ce89-490b-8f89-02ab2f705ffa
-- title:
--   Statements Cone Map Area One
-- statement:
--   Definitions and structural lemmas for Statements Cone Map Area One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeMapAreaOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MeasureTheory
open scoped ENNReal
def ConeMapAreaOne.Statement : Prop :=
  ∀ (n e : ℕ) (U D : Set (Fin e → ℂ)) (v : (Fin e → ℂ) → (Fin n → ℂ))
    (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    IsOpen U → MeasurableSet D → D ⊆ U → DifferentiableOn ℂ v U →
    Set.InjOn (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) {q | q.1 ∈ D ∧ q.2 ≠ 0} →
    Measurable F →
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ y in (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) ''
              {q | q.1 ∈ D ∧ q.2 ≠ 0}, F y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
          ∫⁻ x in D, ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v x)) *
            ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol v x)
end GroundTheory.Heights₂.Heights


