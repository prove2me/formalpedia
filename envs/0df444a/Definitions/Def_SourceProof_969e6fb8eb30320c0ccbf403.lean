-- Prove2me | Definitions.Def_SourceProof_969e6fb8eb30320c0ccbf403
-- name    : SourceProof_969e6fb8eb30320c0ccbf403
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:52:28.895429+00:00
-- url     : https://prove2.me/theorems/8867faea-ff1b-49a5-a348-034eae11cbd4
-- title:
--   LevyStochCalc source module: SourceProof_969e6fb8eb30320c0ccbf403
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indIoc` comes from the `LevyStochCalc.Brownian.ItoIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô integral of an indicator is a Brownian increment

The integrand `1_{(a, b]}` is simple, so its `L²` Itô integral up to a time `t` is the elementary
integral `W_{b ∧ t} − W_{a ∧ t}`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Indicator

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_969e6fb8eb30320c0ccbf403 {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hm : Measurable (Function.uncurry (indIoc Ω a b)))
    (hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b))
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (indIoc Ω a b) hm hp hq t
      =ᵐ[P] fun ω => W.W (min b t) ω - W.W (min a t) ω := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hfun : LevyStochCalc.Brownian.Ito.indIoc Ω 0 b = fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω := by
      funext ω s; rw [_root_.Prove2MeSourceProof.h_29dfa31cfdf118b2f60dc2a9]; rfl
    have hm' : Measurable (Function.uncurry fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω) := by
      rw [← hfun]; exact hm
    have hp' : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω := by
      rw [← hfun]; exact hp
    have hq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT
      have := hq T hT
      rwa [hfun] at this
    have hkey := _root_.Prove2MeSourceProof.h_37464a1abdaa096cc46d9376 W ℱ hℱ (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab)
      (LevyStochCalc.Brownian.Ito.stepIoc₀_adapt ℱ hab) hm' hp' hq' ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun.symm hm' hp' hq' hm hp hq t] at hkey
    exact hkey.trans (Filter.Eventually.of_forall fun ω => LevyStochCalc.Brownian.Ito.stepIoc₀_integralAgainst hab W.W t ω)
  · have hfun : LevyStochCalc.Brownian.Ito.indIoc Ω a b = fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω := by
      funext ω s; rw [LevyStochCalc.Brownian.Ito.stepIoc_eval]; rfl
    have hm' : Measurable (Function.uncurry fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω) := by
      rw [← hfun]; exact hm
    have hp' : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω := by
      rw [← hfun]; exact hp
    have hq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT
      have := hq T hT
      rwa [hfun] at this
    have hkey := _root_.Prove2MeSourceProof.h_37464a1abdaa096cc46d9376 W ℱ hℱ (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab)
      (LevyStochCalc.Brownian.Ito.stepIoc_adapt ℱ ha' hab) hm' hp' hq' ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun.symm hm' hp' hq' hm hp hq t] at hkey
    exact hkey.trans
      (Filter.Eventually.of_forall fun ω => LevyStochCalc.Brownian.Ito.stepIoc_integralAgainst ha' hab W.W t ω)
end Indicator

end LevyStochCalc.Brownian.Ito


