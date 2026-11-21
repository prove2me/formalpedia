-- Prove2me | Definitions.Def_SourceProof_1c13a49ea3c40dba0c47df8d
-- name    : SourceProof_1c13a49ea3c40dba0c47df8d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:01:41.397299+00:00
-- url     : https://prove2.me/theorems/2d4034df-85de-4570-9655-5ab604c6f87f
-- title:
--   LevyStochCalc source module: SourceProof_1c13a49ea3c40dba0c47df8d
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.pairing_cell_eq_zero` comes from the `LevyStochCalc.Brownian.PRPCell` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPCell_F000
import Definitions.Def_SourceProof_6f82a8f1a241e4a2ebbba77b
import Definitions.Def_SourceProof_8947220630d6423d404c65c5
import Definitions.Def_SourceProof_993ce145fd17dba0bc1a4282
import Definitions.Def_SourceProof_da7ea7e203c7e5242a91682e
import Definitions.Def_SourceProof_fb131f2d05ee8dfbbc8425e0

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# One window of the Brownian predictable representation

A square-integrable weight orthogonal to every Itô integral, multiplied by a bounded weight
measurable before a window and having mean zero, stays orthogonal to the character of the
Brownian increment across that window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Cell

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

include hℱ in

theorem _root_.Prove2MeSourceProof.h_1c13a49ea3c40dba0c47df8d
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P) (hZp : PerpItoIntegrals W ℱ hℱ Z)
    {V : Ω → ℂ} (hVm : Measurable V) {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, ‖V ω‖ ≤ Mv)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℂ _ (ℱ a) V)
    (hZV : ∫ ω, Z ω * V ω ∂P = 0) (l : ℝ) :
    ∫ ω, Z ω * V ω * Complex.exp (((l * (W.W b ω - W.W a ω) : ℝ) : ℂ) * Complex.I) ∂P = 0 := by
  classical
  have hb0 : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  have hm := LevyStochCalc.Brownian.Ito.measurable_uncurry_indIoc (Ω := Ω) a b
  have hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (LevyStochCalc.Brownian.Ito.indIoc Ω a b) := by
    rcases eq_or_lt_of_le ha with rfl | ha'
    · exact LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indIoc₀ ℱ hb0
    · exact LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indIoc ℱ ha' hab
  have hq := _root_.Prove2MeSourceProof.h_0d2a3821a25704fa81bdea82 (Ω := Ω) P a b
  obtain ⟨X, hX⟩ := _root_.Prove2MeSourceProof.h_a53c24ec6562d896f4419b97 W ℱ hℱ (LevyStochCalc.Brownian.Ito.indIoc Ω a b) hm hp hq
    (C := 1) zero_le_one (LevyStochCalc.Brownian.Ito.indIoc_le_one a b) hℱ0 hnull
    (X₀ := fun _ => (0 : ℝ)) measurable_const
    (fun _ _ => (0 : ℝ)) measurable_const (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_zero ℱ)
    (B := 0) le_rfl (fun ω s => by simp)
  have hZ1 : Integrable Z P := hZ2.integrable one_le_two
  have hYm : Measurable fun ω => Z ω * V ω := hZm.mul hVm
  have hY : Integrable (fun ω => Z ω * V ω) P :=
    LevyStochCalc.Brownian.Ito.integrable_mul_of_bounded hZ1 hVm.aestronglyMeasurable hVb
  have hXm := hX.measurable_uncurry
  have hX0 := LevyStochCalc.Brownian.Ito.ae_eq_zero_of_isItoVersion_indIoc ha hab hX
  have hXb := LevyStochCalc.Brownian.Ito.ae_eq_increment_of_isItoVersion_indIoc ha hab hX
  -- both trigonometric pairings vanish at the right end of the window
  have key : ∀ g g' : ℝ → ℝ, Continuous g → (∀ x, |g x| ≤ 1) → Continuous g' →
      (∀ x, |g' x| ≤ |l|) →
      (∀ T : ℝ, 0 < T →
        ∀ (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s))
          (hpg : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
            fun ω s => g' (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s)
          (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            (‖g' (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
          (fun ω => g (X T ω) - g (X 0 ω)) =ᵐ[P] fun ω =>
            LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
                (fun ω s => g' (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg T ω
              + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T,
                  -l ^ 2 * g (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s ^ 2 ∂volume) →
      ∫ ω, (fun ω => Z ω * V ω) ω * ((g (X b ω) : ℝ) : ℂ) ∂P = 0 := by
    intro g g' hgc hgb hg'c hg'b hito
    refine _root_.Prove2MeSourceProof.h_993ce145fd17dba0bc1a4282 hXm hX0 hYm hY hZV l hgc hgb ?_ b ⟨hb0.le, le_rfl⟩
    intro t ht0 _
    have hmg := LevyStochCalc.Brownian.Ito.measurable_trig_integrand hX hg'c
    have hpg := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_trig_integrand hX hg'c
    have hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖g' (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
      fun T' hT' => LevyStochCalc.Brownian.Ito.lintegral_sq_trig_integrand_lt_top hg'b (abs_nonneg l) T' hT'
    refine _root_.Prove2MeSourceProof.h_da7ea7e203c7e5242a91682e hXm hX0 hYm hY hZV l hgc hgb
      (A := fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => g' (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) hmg hpg hqg t ω) ?_ ht0 (hito t ht0 hmg hpg hqg)
    exact _root_.Prove2MeSourceProof.h_8947220630d6423d404c65c5 ha hab hZ2 hZp hVm hMv0 hVb hVa
      (K := fun ω s => g' (X s ω)) (hg'c.measurable.comp hXm)
      (hX.progressivelyMeasurable_comp hg'c) (fun ω s => hg'b _)
      hmg hpg hqg ht0
  have hcos := key (fun x => Real.cos (l * x)) (fun x => -l * Real.sin (l * x))
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    (fun x => Real.abs_cos_le_one _)
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).const_mul _)
    (LevyStochCalc.Analysis.abs_neg_mul_sin_scaled_le l)
    (fun T hT hmg hpg hqg =>
      _root_.Prove2MeSourceProof.h_6f82a8f1a241e4a2ebbba77b zero_le_one (LevyStochCalc.Brownian.Ito.indIoc_le_one a b) hX l hmg hpg hqg hT)
  have hsin := key (fun x => Real.sin (l * x)) (fun x => l * Real.cos (l * x))
    (Real.continuous_sin.comp (continuous_const.mul continuous_id))
    (fun x => Real.abs_sin_le_one _)
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).const_mul _)
    (LevyStochCalc.Analysis.abs_mul_cos_scaled_le l)
    (fun T hT hmg hpg hqg =>
      _root_.Prove2MeSourceProof.h_fb131f2d05ee8dfbbc8425e0 zero_le_one (LevyStochCalc.Brownian.Ito.indIoc_le_one a b) hX l hmg hpg hqg hT)
  -- assemble the character from its real and imaginary parts
  have hexp : ∀ x : ℝ, Complex.exp ((x : ℂ) * Complex.I)
      = ((Real.cos x : ℝ) : ℂ) + Complex.I * ((Real.sin x : ℝ) : ℂ) := by
    intro x
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  have hintc : Integrable (fun ω => (Z ω * V ω)
      * ((Real.cos (l * X b ω) : ℝ) : ℂ)) P := by
    refine LevyStochCalc.Brownian.Ito.integrable_mul_of_bounded hY ?_ (c := 1) (fun ω => ?_)
    · exact (Complex.measurable_ofReal.comp (Real.continuous_cos.measurable.comp
        ((hX.measurable b).const_mul l))).aestronglyMeasurable
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
  have hints : Integrable (fun ω => (Z ω * V ω)
      * ((Real.sin (l * X b ω) : ℝ) : ℂ)) P := by
    refine LevyStochCalc.Brownian.Ito.integrable_mul_of_bounded hY ?_ (c := 1) (fun ω => ?_)
    · exact (Complex.measurable_ofReal.comp (Real.continuous_sin.measurable.comp
        ((hX.measurable b).const_mul l))).aestronglyMeasurable
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
  have hrw : ∫ ω, Z ω * V ω
        * Complex.exp (((l * (W.W b ω - W.W a ω) : ℝ) : ℂ) * Complex.I) ∂P
      = ∫ ω, ((Z ω * V ω) * ((Real.cos (l * X b ω) : ℝ) : ℂ)
          + Complex.I * ((Z ω * V ω) * ((Real.sin (l * X b ω) : ℝ) : ℂ))) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hXb] with ω hω
    rw [← hω, hexp (l * X b ω)]
    ring
  rw [hrw, integral_add hintc (hints.const_mul Complex.I), hcos, integral_const_mul, hsin,
    mul_zero, add_zero]
end Cell

end LevyStochCalc.Brownian.Ito


