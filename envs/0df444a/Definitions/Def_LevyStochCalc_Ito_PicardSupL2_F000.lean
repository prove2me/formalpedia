-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardSupL2_F000
-- name    : LevyStochCalc_Ito_PicardSupL2_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:10:16.500028+00:00
-- url     : https://prove2.me/theorems/fab10b77-74df-4d82-b71a-9126f745cb45
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardSupL2
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardSupL2. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F000
import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F001
import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F002
import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F003
import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F004
import Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F000
import Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F001
import Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F002
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F003
import Definitions.Def_SourceProof_d76df0724e08b30159a31ac0

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The `S²` bound for the Picard step

`LevyStochCalc.Ito.Setting.JumpDiffusion.sup_L2` asks for `𝔼[sup_{t ≤ T} ‖X_t‖²] < ∞`, the `S²`
norm, which is stronger than the weighted supremum of `L²` norms the Picard space carries. The
Picard step splits into a drift, `d` Brownian integrals and a compensated-Poisson integral; the
drift is bounded pathwise by its own total variation over the window, and each stochastic
component is a martingale, so Doob's `L²` inequality over the dyadic points applies. Only the
dyadic form of Doob is available here, because the stochastic integrals are càdlàg only up to
modification.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### An elementary two-term bound -/

/-- A squared sum of two extended reals, up to the constant `4`. -/
theorem sq_add_le_four_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have h1 : a + b ≤ 2 * (a ⊔ b) := by
    calc a + b ≤ (a ⊔ b) + (a ⊔ b) := add_le_add le_sup_left le_sup_right
      _ = 2 * (a ⊔ b) := by ring
  have h2 : (a ⊔ b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases max_choice a b with h | h <;> rw [h]
    · exact le_add_right le_rfl
    · exact le_add_left le_rfl
  calc (a + b) ^ 2 ≤ (2 * (a ⊔ b)) ^ 2 := pow_le_pow_left' h1 2
    _ = 4 * (a ⊔ b) ^ 2 := by rw [mul_pow]; norm_num
    _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl h2
/-- A squared sum of three extended reals, up to the constant `16`. -/
theorem sq_add3_le_sixteen_mul (a b c : ℝ≥0∞) : (a + b + c) ^ 2 ≤ 16 * (a ^ 2 + b ^ 2 + c ^ 2) :=
  calc (a + b + c) ^ 2 ≤ 4 * ((a + b) ^ 2 + c ^ 2) := sq_add_le_four_mul _ _
    _ ≤ 4 * (4 * (a ^ 2 + b ^ 2) + c ^ 2) :=
        mul_le_mul' le_rfl (add_le_add (sq_add_le_four_mul a b) le_rfl)
    _ = 16 * (a ^ 2 + b ^ 2) + 4 * c ^ 2 := by ring
    _ ≤ 16 * (a ^ 2 + b ^ 2) + 16 * c ^ 2 :=
        add_le_add le_rfl (mul_le_mul' (by norm_num) le_rfl)
    _ = 16 * (a ^ 2 + b ^ 2 + c ^ 2) := by ring
/-! ### The drift component -/

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The drift component is dominated over the window by its own total variation there. -/
theorem iSup_dyadicRunMax_drift_le
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n) {T' : ℝ} (hT' : 0 ≤ T') {ω : Ω}
    (hint : MeasureTheory.IntegrableOn (fun s => coeffs.μ s (X s ω) i)
      (Set.Icc (0 : ℝ) T') volume) :
    (⨆ m, (‖dyadicRunMax (fun t ω => picardStep_drift coeffs X x₀ t ω i) T' m ω‖₊ : ℝ≥0∞))
      ≤ (‖x₀ i‖₊ : ℝ≥0∞)
        + (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞) := by
  refine iSup_dyadicRunMax_le_of_bound hT' fun t ht => ?_
  have hval : picardStep_drift coeffs X x₀ t ω i
      = x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i := rfl
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T' := Set.Icc_subset_Icc le_rfl ht.2
  have hnn' : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) T')]
      fun s => ‖coeffs.μ s (X s ω) i‖ :=
    Filter.Eventually.of_forall fun _ => norm_nonneg _
  have hmono : ∫ s in Set.Icc (0 : ℝ) t, ‖coeffs.μ s (X s ω) i‖
      ≤ ∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖ :=
    MeasureTheory.setIntegral_mono_set hint.norm hnn' hsub.eventuallyLE
  have hnorm : ‖∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖
      ≤ ∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖ :=
    le_trans (MeasureTheory.norm_integral_le_integral_norm _) hmono
  rw [hval]
  refine le_trans (by rw [← ENNReal.coe_add]; exact ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _))
    (add_le_add le_rfl ?_)
  have hnn : (0 : ℝ) ≤ ∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖ :=
    MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  refine ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp ?_)
  rw [coe_nnnorm, coe_nnnorm,
    show ‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖
        = ∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖ from
      by rw [Real.norm_eq_abs, abs_of_nonneg hnn]]
  exact hnorm
omit [MeasurableSpace E] in
/-- The drift dominator is square integrable. -/
theorem lintegral_sq_drift_bound_lt_top
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n) {T' : ℝ} (hT' : 0 ≤ T')
    (hμm : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, ((‖x₀ i‖₊ : ℝ≥0∞)
        + (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
  have hfin' : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hfin
    exact lintegral_congr fun ω => lintegral_congr fun s => by rw [nnnorm_norm]
  have hkey := _root_.Prove2MeSourceProof.h_190a5767e8f1b936b4a6a09f (P := P)
    (f := fun ω s => ‖coeffs.μ s (X s ω) i‖) hμm.norm hT' hfin'
  have hbfin : ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞) ^ 2 ∂P
      < ⊤ := lt_of_le_of_lt hkey (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin')
  have hbm : Measurable fun ω : Ω =>
      (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞) ^ 2 :=
    (ENNReal.continuous_coe.measurable.comp
      (measurable_setIntegral_slice hμm.norm T').nnnorm).pow_const 2
  refine lt_of_le_of_lt (lintegral_mono fun ω => sq_add_le_four_mul _ _) ?_
  rw [lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
    lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr
    ⟨ENNReal.pow_lt_top ENNReal.coe_lt_top, hbfin⟩)
/-! ### The stochastic components -/

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]

/-- Doob's inequality for the jump component of the Picard step. -/
theorem lintegral_sq_iSup_jump_le
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 ≤ T') :
    ∫⁻ ω, (⨆ m, (‖dyadicRunMax
        (fun t ω => picardStep_jump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i)
        T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  have hmart : MeasureTheory.Martingale
      (fun t ω => picardStep_jump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i)
      ℱ.rightCont P :=
    LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral_rightCont N ℱ hℱN
      (fun ω s e => coeffs.γ s (X s ω) e i) (h_meas i) (h_progMeas i) (h_sq i)
  refine le_trans (lintegral_iSup_dyadicRunMax_sq_le hmart hT') ?_
  rw [lintegral_sq_picardStep_jump_eq N ℱ hℱN coeffs X h_meas h_progMeas h_sq i hT']
omit [MeasurableSpace E] in
/-- Doob's inequality for one Brownian coordinate of the Picard step. -/
theorem lintegral_sq_iSup_brownian_coord_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) (j : Fin d) {T' : ℝ} (hT' : 0 ≤ T') :
    ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω =>
        LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j)
          (h_meas i j) (h_progMeas i j) (h_sq i j) t ω) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 4 * ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j)
          (h_meas i j) (h_progMeas i j) (h_sq i j) T' ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  obtain ⟨F, hF⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral (W.W j) ℱ (hℱW j)
    (fun ω' s => coeffs.σ s (X s ω') i j) (h_meas i j) (h_progMeas i j) (h_sq i j)
  exact lintegral_iSup_dyadicRunMax_sq_le hF hT'
/-! ### The whole step -/

omit [MeasurableSpace E] in
/-- Slice measurability of one Brownian coordinate's integral. -/
theorem measurable_brownianIntegral_slice
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) (j : Fin d) (t : ℝ) :
    Measurable fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j) (h_meas i j) (h_progMeas i j) (h_sq i j) t ω := by
  obtain ⟨F, hF⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral (W.W j) ℱ (hℱW j)
    (fun ω' s => coeffs.σ s (X s ω') i j) (h_meas i j) (h_progMeas i j) (h_sq i j)
  exact (hF.stronglyMeasurable t).measurable.mono (F.le t) le_rfl
omit [MeasurableSpace E] in
/-- The dyadic supremum of the Brownian component, summed over the driving coordinates. -/
theorem lintegral_sq_iSup_diffusion_lt_top
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω =>
        picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i)
        T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
  set g : Fin d → ℝ → Ω → ℝ := fun j t ω =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j) t ω with hg
  have hunfold : (fun t (ω : Ω) =>
      picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i)
      = fun t ω => ∑ j : Fin d, g j t ω := rfl
  have hmeas : ∀ j : Fin d, ∀ t : ℝ, Measurable (g j t) := fun j t =>
    measurable_brownianIntegral_slice W ℱ hℱW coeffs X h_meas h_progMeas h_sq i j t
  have hsupm : ∀ j : Fin d, Measurable fun ω =>
      (⨆ m, (‖dyadicRunMax (g j) T' m ω‖₊ : ℝ≥0∞)) ^ 2 :=
    fun j => (Measurable.iSup fun m => measurable_enorm_dyadicRunMax (hmeas j) T' m).pow_const 2
  calc ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω => ∑ j : Fin d, g j t ω) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ ∫⁻ ω, ((Finset.univ.card : ℝ≥0∞) ^ 2
          * ∑ j : Fin d, (⨆ m, (‖dyadicRunMax (g j) T' m ω‖₊ : ℝ≥0∞)) ^ 2) ∂P :=
        lintegral_mono fun ω => le_trans
          (pow_le_pow_left' (iSup_dyadicRunMax_sum_le Finset.univ g T' ω) 2)
          (_root_.Prove2MeSourceProof.h_d76df0724e08b30159a31ac0 Finset.univ _)
    _ = (Finset.univ.card : ℝ≥0∞) ^ 2
          * ∑ j : Fin d, ∫⁻ ω, (⨆ m, (‖dyadicRunMax (g j) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum _ fun j _ => hsupm j]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (by simp) (ENNReal.sum_lt_top.mpr fun j _ => ?_)
        refine lt_of_le_of_lt (lintegral_sq_iSup_brownian_coord_le W ℱ hℱW coeffs X
          h_meas h_progMeas h_sq i j hT'.le) ?_
        refine ENNReal.mul_lt_top (by norm_num) ?_
        refine lt_of_le_of_lt ?_ (h_sq i j T' hT')
        exact le_of_eq (LevyStochCalc.Brownian.Ito.itoIsometry (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j) T' hT'
          (h_meas i j) (h_progMeas i j) (h_sq i j))
/-! ### The `S²` bound for the raw self-map -/

end LevyStochCalc.Ito.Picard


