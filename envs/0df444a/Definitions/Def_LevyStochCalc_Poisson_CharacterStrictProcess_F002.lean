-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F002
-- name    : LevyStochCalc_Poisson_CharacterStrictProcess_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:01:17.282512+00:00
-- url     : https://prove2.me/theorems/232f2e0a-48f7-40b5-b1fc-42e02facb3dc
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterStrictProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterStrictProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F001
import Definitions.Def_SourceProof_35d8365844de2771203e553f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The strict-past character as a progressively measurable process

The predictable representative of the strictly-past window sum, evaluated at a fixed mark of the
window and at the time clamped to the horizon, is a jointly measurable and progressively
measurable process. For a family carried strictly before the horizon it is exactly the exponent
of the strict-past character at every time, so the strict-past character is itself progressively
measurable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Evaluation

end Evaluation

section Clamped

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  {A : Set E} {b T : ℝ}

theorem norm_charStrictPred (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ) (e₀ : E) (s : ℝ)
    (ω : Ω) : ‖charStrictPred N w Bfam A T e₀ s ω‖ = 1 := by
  rw [charStrictPred, Complex.norm_exp_I_mul_ofReal]
theorem abs_charStrictPred_re_le (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ) (e₀ : E) (s : ℝ)
    (ω : Ω) : |(charStrictPred N w Bfam A T e₀ s ω).re| ≤ 1 := by
  have := Complex.abs_re_le_norm (charStrictPred N w Bfam A T e₀ s ω)
  rwa [norm_charStrictPred N w Bfam A T e₀ s ω] at this
theorem abs_charStrictPred_im_le (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ) (e₀ : E) (s : ℝ)
    (ω : Ω) : |(charStrictPred N w Bfam A T e₀ s ω).im| ≤ 1 := by
  have := Complex.abs_im_le_norm (charStrictPred N w Bfam A T e₀ s ω)
  rwa [norm_charStrictPred N w Bfam A T e₀ s ω] at this
variable (hℱ : IsPoissonFiltration N ℱ) (hBm : ∀ j, MeasurableSet (Bfam j))
  (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)

include hℱ hBm hA hAν in
/-- The predictable representative of the strict-past character is jointly measurable. -/
theorem measurable_uncurry_charStrictPred (T : ℝ) (e₀ : E) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      charStrictPred N w Bfam A T e₀ s ω) := by
  have hpm : Measurable fun p : Ω × ℝ × E => predStrict N w Bfam A T p.1 p.2.1 p.2.2 :=
    (markedPredictable_predStrict N hℱ w hBm hA hAν T).mono
      (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hg : Measurable fun p : Ω × ℝ => (p.1, (min p.2 T, e₀)) :=
    measurable_fst.prodMk ((measurable_snd.min measurable_const).prodMk measurable_const)
  have hf := hpm.comp hg
  exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hf))
omit [IsProbabilityMeasure P] [SigmaFinite ν] [Fintype ι] in
theorem exp_I_mul_ofReal_re (x : ℝ) : (Complex.exp (Complex.I * (x : ℂ))).re = Real.cos x := by
  rw [mul_comm, Complex.exp_ofReal_mul_I_re]
omit [IsProbabilityMeasure P] [SigmaFinite ν] [Fintype ι] in
theorem exp_I_mul_ofReal_im (x : ℝ) : (Complex.exp (Complex.I * (x : ℂ))).im = Real.sin x := by
  rw [mul_comm, Complex.exp_ofReal_mul_I_im]
omit [IsProbabilityMeasure P] [SigmaFinite ν] [Fintype ι] in
/-- A constant process is progressively measurable. -/
theorem progressivelyMeasurable_const' (c : ℝ) :
    Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => c :=
  _root_.Prove2MeSourceProof.h_35d8365844de2771203e553f
    (MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous
      (fun _ => stronglyMeasurable_const) fun _ => continuous_const)
section Parts

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ)

end Parts

end Clamped

end LevyStochCalc.Poisson


