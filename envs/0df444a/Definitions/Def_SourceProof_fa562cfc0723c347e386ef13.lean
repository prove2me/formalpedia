-- Prove2me | Definitions.Def_SourceProof_fa562cfc0723c347e386ef13
-- name    : SourceProof_fa562cfc0723c347e386ef13
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:12:22.851073+00:00
-- url     : https://prove2.me/theorems/376b3d4a-d897-4bf7-8e73-6a8f40b6bc77
-- title:
--   LevyStochCalc source module: SourceProof_fa562cfc0723c347e386ef13
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.norm_charPairing_le_integral` comes from the `LevyStochCalc.Poisson.CharacterGronwall` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterGronwall_F000
import Definitions.Def_SourceProof_29aeb1b76d0477f3944256c5

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing with the characters satisfies a Grönwall inequality

For a square-integrable weight of mean zero orthogonal to every compensated integral over the
horizon, the pairing `u(t) = 𝔼[r · χ_t]` with the character of the window counts up to `t` is a
window integral of the marks times the pairings at earlier times. Its norm is therefore bounded by
`2 ν(A)` times its own running integral, and it is a bounded measurable function of the time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Pairing

end Pairing

section Bound


theorem _root_.Prove2MeSourceProof.h_fa562cfc0723c347e386ef13 (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {r : Ω → ℝ} (hr2 : MemLp r 2 P)
    (hr0 : ∫ ω, r ω ∂P = 0)
    (hperp : ∀ G : Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, r ω * G.integral N hℱ ω ∂P = 0)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A)
    (hAne : A.Nonempty) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖charPairing N w Bfam r t‖
      ≤ 2 * (ν A).toReal * ∫ s in (0 : ℝ)..t, ‖charPairing N w Bfam r s‖ := by
  have hr1 : Integrable r P := hr2.integrable one_le_two
  have hWm : MeasurableSet (Set.Ioc (0 : ℝ) T ×ˢ A) := measurableSet_Ioc.prod hA
  have hSm : MeasurableSet (Set.Ioc (0 : ℝ) t ×ˢ A) := measurableSet_Ioc.prod hA
  have hSW : Set.Ioc (0 : ℝ) t ×ˢ A ⊆ Set.Ioc (0 : ℝ) T ×ˢ A :=
    Set.prod_mono (Set.Ioc_subset_Ioc_right ht.2) le_rfl
  have hUt : IntegrableOn (fun s => ‖LevyStochCalc.Poisson.charPairing N w Bfam r s‖) (Set.Ioc 0 t) volume :=
    (LevyStochCalc.Poisson.integrableOn_norm_charPairing N hℱ hr1 w hBm hA hAν T hAne).mono_set
      (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2))
  have hUint : IntegrableOn (fun q : ℝ × E => 2 * ‖LevyStochCalc.Poisson.charPairing N w Bfam r q.1‖)
      (Set.Ioc (0 : ℝ) t ×ˢ A) (LevyStochCalc.Poisson.referenceIntensity ν) :=
    (LevyStochCalc.Poisson.integrableOn_prod_of_time (ν := ν) hUt hAν).const_mul 2
  calc ‖LevyStochCalc.Poisson.charPairing N w Bfam r t‖
      = ‖∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          LevyStochCalc.Poisson.charMark w Bfam t q * LevyStochCalc.Poisson.charPairing N w Bfam r q.1 ∂(LevyStochCalc.Poisson.referenceIntensity ν)‖ := by
        rw [LevyStochCalc.Poisson.charPairing_eq_window_integral N hℱ hT hr2 hr0 hperp w hBm hA hAν hBsub ht.2]
    _ ≤ ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          ‖LevyStochCalc.Poisson.charMark w Bfam t q * LevyStochCalc.Poisson.charPairing N w Bfam r q.1‖ ∂(LevyStochCalc.Poisson.referenceIntensity ν) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          (Set.Ioc (0 : ℝ) t ×ˢ A).indicator (fun q => 2 * ‖LevyStochCalc.Poisson.charPairing N w Bfam r q.1‖) q
          ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg _)
          (hUint.integrable_indicator hSm).integrableOn ?_
        rw [Filter.EventuallyLE, ae_restrict_iff' hWm]
        refine Filter.Eventually.of_forall fun q hq => ?_
        rcases le_or_gt q.1 t with hqt | hqt
        · have hqS : q ∈ Set.Ioc (0 : ℝ) t ×ˢ A := ⟨⟨hq.1.1, hqt⟩, hq.2⟩
          rw [Set.indicator_of_mem hqS, norm_mul]
          exact mul_le_mul_of_nonneg_right (_root_.Prove2MeSourceProof.h_29aeb1b76d0477f3944256c5 w Bfam t q) (norm_nonneg _)
        · rw [LevyStochCalc.Poisson.charMark_eq_zero w Bfam hqt, zero_mul, norm_zero]
          exact Set.indicator_nonneg (fun q _ => by positivity) q
    _ = ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, 2 * ‖LevyStochCalc.Poisson.charPairing N w Bfam r q.1‖
          ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
        rw [setIntegral_indicator hSm, Set.inter_eq_right.mpr hSW]
    _ = 2 * (ν A).toReal * ∫ s in (0 : ℝ)..t, ‖LevyStochCalc.Poisson.charPairing N w Bfam r s‖ := by
        rw [MeasureTheory.integral_const_mul, LevyStochCalc.Poisson.setIntegral_prod_of_time hUt hAν,
          intervalIntegral.integral_of_le ht.1, mul_assoc]
end Bound

end LevyStochCalc.Poisson


