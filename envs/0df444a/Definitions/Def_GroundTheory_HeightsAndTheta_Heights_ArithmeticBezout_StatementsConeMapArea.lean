-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapArea
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapArea
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:48.963234+00:00
-- url     : https://prove2.me/theorems/a37296ce-7a0d-446d-baf3-73e99dde56ee
-- title:
--   Statements Cone Map Area
-- statement:
--   Definitions and structural lemmas for Statements Cone Map Area, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeMapArea.lean

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
def ConeMapArea.Statement : Prop :=
  ∀ (n e : ℕ) (ι : Type) [Countable ι] (U D : ι → Set (Fin e → ℂ))
    (v : ι → (Fin e → ℂ) → (Fin n → ℂ)) (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    (∀ i, IsOpen (U i) ∧ MeasurableSet (D i) ∧ D i ⊆ U i ∧ DifferentiableOn ℂ (v i) (U i)) →
    Set.InjOn (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1))
      {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0} →
    Measurable F →
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ y in (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
              {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0}, F y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
          ∑' i, ∫⁻ x in D i, ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v i x)) *
            ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) x)
end GroundTheory.Heights₂.Heights


