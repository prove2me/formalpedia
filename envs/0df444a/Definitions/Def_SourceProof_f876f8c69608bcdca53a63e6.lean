-- Prove2me | Definitions.Def_SourceProof_f876f8c69608bcdca53a63e6
-- name    : SourceProof_f876f8c69608bcdca53a63e6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:45:00.419793+00:00
-- url     : https://prove2.me/theorems/722e4855-8021-488a-8f4c-0453dcd94de6
-- title:
--   LevyStochCalc source module: SourceProof_f876f8c69608bcdca53a63e6
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.exists_mul_simple` comes from the `LevyStochCalc.Brownian.ItoAlgebraProduct` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F002
import Definitions.Def_SourceProof_892fcf8c8493750469597892
import Definitions.Def_SourceProof_b0aff0c8496672a11de8686b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Products of simple integrands and elementary integrals against a process

Two simple integrands with a common final partition point multiply to a simple integrand carried
on their common refinement, whose evaluation is the pointwise product of the evaluations and
whose adaptedness is inherited; summing the increments of the elementary integral of one against
the coefficients of the other is the elementary integral of that product, and the difference
between an elementary integral and an `L²` Itô integral obeys the Itô isometry.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section SimpleVsGeneral

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end SimpleVsGeneral


theorem _root_.Prove2MeSourceProof.h_f876f8c69608bcdca53a63e6
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T₁ T₂ : ℝ} (G : SimplePredictable Ω T₁) (K : SimplePredictable Ω T₂)
    (h_adaptG : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    (h_adaptK : ∀ i : Fin K.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (K.partition i.castSucc)) (K.ξ i)) :
    ∃ (T₃ : ℝ) (Q : SimplePredictable Ω T₃),
      (∀ i : Fin Q.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (Q.partition i.castSucc)) (Q.ξ i))
      ∧ (∀ s ω, Q.eval s ω = G.eval s ω * K.eval s ω)
      ∧ (∀ t ω, G.integralAgainst (fun u ω' => simpleIntegral W K u ω') t ω
          = simpleIntegral W Q t ω) := by
  have hG : G.partition (Fin.last G.N)
      < max (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)) + 1 := by
    have := le_max_left (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)); linarith
  have hK : K.partition (Fin.last K.N)
      < max (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)) + 1 := by
    have := le_max_right (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)); linarith
  have h_eq : (G.appendInterval hG).partition (Fin.last (G.appendInterval hG).N)
      = (K.appendInterval hK).partition (Fin.last (K.appendInterval hK).N) :=
    (G.appendInterval_partition_last hG).trans (K.appendInterval_partition_last hK).symm
  refine ⟨_, (G.appendInterval hG).mul_on_common (K.appendInterval hK) h_eq, ?_, ?_, ?_⟩
  · exact LevyStochCalc.Brownian.Ito.SimplePredictable.mul_on_common_adapt ℱ _ _ h_eq
      (G.appendInterval_adapt ℱ hG h_adaptG) (K.appendInterval_adapt ℱ hK h_adaptK)
  · intro s ω
    rw [_root_.Prove2MeSourceProof.h_892fcf8c8493750469597892, (_root_.Prove2MeSourceProof.h_3d4df4df753a663d9a385c25 G) hG,
      (_root_.Prove2MeSourceProof.h_3d4df4df753a663d9a385c25 K) hK]
  · intro t ω
    rw [← _root_.Prove2MeSourceProof.h_b0aff0c8496672a11de8686b W (G.appendInterval hG)
      (K.appendInterval hK) h_eq t ω]
    have hKfun : (fun u (ω' : Ω) => LevyStochCalc.Brownian.Ito.simpleIntegral W K u ω')
        = fun u ω' => LevyStochCalc.Brownian.Ito.simpleIntegral W (K.appendInterval hK) u ω' := by
      funext u ω'; exact ((fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_c5a0aac77ea3887770fece7e p2mMethodArg0 K) W hK u ω').symm
    rw [hKfun, ← G.appendInterval_integralAgainst hG
      (fun u ω' => LevyStochCalc.Brownian.Ito.simpleIntegral W (K.appendInterval hK) u ω') t ω]
    rfl
end LevyStochCalc.Brownian.Ito


