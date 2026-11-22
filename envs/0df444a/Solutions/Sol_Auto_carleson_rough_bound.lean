-- Prove2me | solution 1 for Auto.carleson_rough_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:12:47.012845+00:00
-- url     : https://prove2.me/submissions/c6fc3b19-81ca-4449-8440-6d546deb6c33

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carlesonBump_eq_zero
public import Theorems.Thm_Auto_integrable_of_norm_le_of_vanish
public import Theorems.Thm_Auto_hasCompactSupport_of_vanish
public import Theorems.Thm_Auto_carlesonWeight_nonneg
public import Theorems.Thm_Auto_measurable_carlesonWeight
public import Theorems.Thm_Auto_integrable_carlesonWeight
public import Theorems.Thm_P2M_Auto_contDiff_carlesonF__9fa96f04780b
public import Theorems.Thm_Auto_abs_sin_mul_div_le
public import Theorems.Thm_Auto_carleson_smooth_bound
public import Theorems.Thm_Auto_eLpNorm_toReal_le_of_strip
public import Theorems.Thm_P2M_Auto_eLpNorm_carlesonF__le_0be6ee33c933
public import Theorems.Thm_Auto_contDiff_carlesonMoll
public import Theorems.Thm_Auto_norm_carlesonMoll_le
public import Theorems.Thm_Auto_carlesonMoll_eq_zero
public import Theorems.Thm_Auto_ae_tendsto_carlesonMoll
public import Theorems.Thm_Auto_ae_fst_of_ae
public import Theorems.Thm_Auto_ae_sub_of_ae
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution (L : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Set ℝ) (ν : ℝ → ℝ) (g : ℝ → ℂ)
    (R V B : ℝ), MeasurableSet F → F ⊆ Icc (-R) R → Measurable ν → (∀ x, |ν x| ≤ V) →
    Measurable g → (∀ x, ‖g x‖ ≤ B) → (∀ x, L < |x| → g x = 0) →
    ‖carlesonForm (F.indicator 1) ν g‖ ≤ K * B * (volume F).toReal ^ (2 / 3 : ℝ) := by
  obtain ⟨C, hC, hsm⟩ := carleson_smooth_bound
  set Vb := (volume (carlesonBox (L + 1))).toReal
  refine ⟨C * 4 ^ (1 / 3 : ℝ) * Vb ^ (1 / 3 : ℝ) * 18 ^ (1 / 3 : ℝ), by positivity, ?_⟩
  intro F ν g R V B hF hFR hν hνV hg hgB hgL
  have hB : 0 ≤ B := (norm_nonneg _).trans (hgB 0)
  set a : ℝ → ℝ := F.indicator 1
  set ν' : ℝ → ℝ := (Icc (-R) R).indicator ν
  have hRF : ∀ x, R < |x| → x ∉ F := fun x hx hxF =>
    (not_le.mpr hx) (abs_le.mpr (hFR hxF))
  have ha_m : Measurable a := measurable_const.indicator hF
  have hν'_m : Measurable ν' := hν.indicator measurableSet_Icc
  have ha_b : ∀ x, ‖a x‖ ≤ 1 := fun x => by by_cases hx : x ∈ F <;> simp [a, hx]
  have ha_z : ∀ x, R < |x| → a x = 0 := fun x hx => indicator_of_notMem (hRF x hx) _
  have hν'_b : ∀ x, ‖ν' x‖ ≤ V := fun x => by
    by_cases hx : x ∈ Icc (-R) R
    · simpa [ν', hx] using hνV x
    · simpa [ν', hx] using (abs_nonneg _).trans (hνV x)
  have hν'_z : ∀ x, R < |x| → ν' x = 0 := fun x hx =>
    indicator_of_notMem (show x ∉ Icc (-R) R from fun h => (not_le.mpr hx) (abs_le.mpr h)) _
  have ha_i := integrable_of_norm_le_of_vanish ha_m.aestronglyMeasurable ha_b ha_z
  have hν'_i := integrable_of_norm_le_of_vanish hν'_m.aestronglyMeasurable hν'_b hν'_z
  have hg_i := integrable_of_norm_le_of_vanish hg.aestronglyMeasurable hgB hgL
  set ak := fun k => carlesonMoll k a
  set νk := fun k => carlesonMoll k ν'
  set gk := fun k => carlesonMoll k g
  have hak_s : ∀ k, ContDiff ℝ ∞ (ak k) := fun k => contDiff_carlesonMoll k ha_i.locallyIntegrable
  have hνk_s : ∀ k, ContDiff ℝ ∞ (νk k) := fun k =>
    contDiff_carlesonMoll k hν'_i.locallyIntegrable
  have hgk_s : ∀ k, ContDiff ℝ ∞ (gk k) := fun k => contDiff_carlesonMoll k hg_i.locallyIntegrable
  have hak_b : ∀ k x, ‖ak k x‖ ≤ 1 := fun k => norm_carlesonMoll_le k ha_b
  have hνk_b : ∀ k x, ‖νk k x‖ ≤ V := fun k => norm_carlesonMoll_le k hν'_b
  have hgk_b : ∀ k x, ‖gk k x‖ ≤ B := fun k => norm_carlesonMoll_le k hgB
  have hak_z : ∀ k x, R + 1 < |x| → ak k x = 0 := fun k x => carlesonMoll_eq_zero k ha_z
  have hgk_z : ∀ k x, L + 1 < |x| → gk k x = 0 := fun k x => carlesonMoll_eq_zero k hgL
  have hak_3 : ∀ k, Integrable fun x => |ak k x| ^ 3 := fun k =>
    ((hak_s k).continuous.abs.pow 3).integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanish (A := R + 1) fun x hx => by simp [hak_z k x hx])
  set I := fun k => ∫ x, |ak k x| ^ 3
  set v := (volume F).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hI : Tendsto I atTop (𝓝 v) := by
    have hva : v = ∫ x, |a x| ^ 3 := by
      have : (fun x => |a x| ^ 3) = F.indicator 1 := by
        ext x
        by_cases hx : x ∈ F <;> simp [a, hx]
      rw [this, integral_indicator_one hF]
      rfl
    rw [hva]
    refine tendsto_integral_of_dominated_convergence ((Icc (-(R + 1)) (R + 1)).indicator 1)
      (fun k => (hak_3 k).aestronglyMeasurable)
      ((integrable_indicator_iff measurableSet_Icc).mpr
        (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Icc]))) (fun k => ae_of_all _ fun x => ?_) ?_
    · by_cases hx : x ∈ Icc (-(R + 1)) (R + 1)
      · rw [indicator_of_mem hx, Pi.one_apply, Real.norm_eq_abs, abs_pow, abs_abs]
        exact pow_le_one₀ (abs_nonneg _) (hak_b k x)
      · rw [hak_z k x (lt_of_not_ge fun h => hx (abs_le.mp h))]
        simp only [abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, norm_zero]
        exact indicator_nonneg (fun _ _ => zero_le_one) _
    · filter_upwards [ae_tendsto_carlesonMoll ha_i.locallyIntegrable] with x hx
      exact ((continuous_abs.tendsto _).comp hx).pow 3
  have hk : ∀ k, ‖carlesonForm (ak k) (νk k) (gk k)‖ ≤
      C * (2 * 2 * I k) ^ (1 / 3 : ℝ) * (B * Vb ^ (1 / 3 : ℝ)) *
        (2 * 9 * I k) ^ (1 / 3 : ℝ) := by
    intro k
    refine (hsm (ak k) (νk k) (gk k) (R + 1) (L + 1) (hak_s k) (hνk_s k) (hgk_s k) (hak_z k)
      (hgk_z k)).trans ?_
    have h₀ : (eLpNorm (carlesonF₀ (ak k) (νk k) 1) 3 volume).toReal ≤
        (2 * 2 * I k) ^ (1 / 3 : ℝ) := by
      refine eLpNorm_toReal_le_of_strip (c := 1 / 2) (by norm_num) (hak_s k).continuous.measurable
        (hak_3 k) (fun p => ?_) (fun p hp => ?_)
      · simp only [carlesonF₀, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
          Real.norm_eq_abs, mul_one, abs_of_nonneg carlesonBump₀.nonneg]
        exact mul_le_of_le_one_right (abs_nonneg _) carlesonBump₀.le_one
      · rw [carlesonF₀, carlesonBump_eq_zero carlesonBump₀ (x := p.2 + p.1 / 2)
          (by change (2 : ℝ) ≤ _; rw [show p.2 + p.1 / 2 = p.2 + 1 / 2 * p.1 by ring]; exact hp.le)]
        simp
    have h₁ := eLpNorm_carlesonF₁_le hB (hgk_b k) (hgk_z k)
    have h₂ : (eLpNorm (carlesonF₂ (ak k) (νk k) 1) 3 volume).toReal ≤
        (2 * 9 * I k) ^ (1 / 3 : ℝ) := by
      rw [Measure.volume_eq_prod, ← eLpNorm_comp_measurePreserving
        (contDiff_carlesonF₂ (hak_s k) (hνk_s k) 1).continuous.aestronglyMeasurable
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))]
      refine eLpNorm_toReal_le_of_strip (c := 1 / 2) (by norm_num) (hak_s k).continuous.measurable
        (hak_3 k) (fun p => ?_) (fun p hp => ?_)
      · simp only [Function.comp, Prod.fst_swap, Prod.snd_swap, carlesonF₂, norm_mul,
          Complex.norm_real, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs, mul_one,
          abs_of_nonneg carlesonBump₁.nonneg]
        exact mul_le_of_le_one_right (abs_nonneg _) carlesonBump₁.le_one
      · simp only [Function.comp, Prod.fst_swap, Prod.snd_swap, carlesonF₂]
        rw [carlesonBump_eq_zero carlesonBump₁ (x := p.2 + p.1 / 2)
          (by change (9 : ℝ) ≤ _; rw [show p.2 + p.1 / 2 = p.2 + 1 / 2 * p.1 by ring]; exact hp.le)]
        simp
    have e₀ := ENNReal.toReal_nonneg (a := eLpNorm (carlesonF₀ (ak k) (νk k) 1) 3 volume)
    have e₁ := ENNReal.toReal_nonneg (a := eLpNorm (carlesonF₁ (gk k)) 3 volume)
    have e₂ := ENNReal.toReal_nonneg (a := eLpNorm (carlesonF₂ (ak k) (νk k) 1) 3 volume)
    gcongr
  have hw := measurable_carlesonWeight
  have hform : Tendsto (fun k => carlesonForm (ak k) (νk k) (gk k)) atTop
      (𝓝 (carlesonForm a ν' g)) := by
    set bd : ℝ × ℝ → ℝ := fun p =>
      (Icc (-(R + 1)) (R + 1)).indicator (fun _ => B * V) p.1 * carlesonWeight p.2
    have hbd : Integrable bd := ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (C := B * V) (by simp [Real.volume_Icc]))).mul_prod
        integrable_carlesonWeight
    refine tendsto_integral_of_dominated_convergence bd (fun k => Measurable.aestronglyMeasurable
      (by
        have := (hak_s k).continuous.measurable
        have := (hνk_s k).continuous.measurable
        have := (hgk_s k).continuous.measurable
        fun_prop)) hbd (fun k => ae_of_all _ fun p => ?_) ?_
    · simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      rw [mul_div_assoc, abs_mul, abs_of_nonneg (carlesonWeight_nonneg _)]
      by_cases hx : p.1 ∈ Icc (-(R + 1)) (R + 1)
      · simp only [bd, indicator_of_mem hx]
        have h₁ := abs_sin_mul_div_le (νk k p.1) p.2
        have h₂ := hgk_b k (p.1 - p.2)
        have h₃ := carlesonWeight_nonneg p.2
        have h₄ : |ak k p.1| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) (hak_b k p.1)
        have h₅ : |νk k p.1| ≤ V := hνk_b k p.1
        calc |ak k p.1| ^ 2 * ‖gk k (p.1 - p.2)‖ *
              (carlesonWeight p.2 * |Real.sin (νk k p.1 * p.2) / p.2|)
            ≤ 1 * B * (carlesonWeight p.2 * V) := by
              gcongr
              exact h₁.trans h₅
          _ = B * V * carlesonWeight p.2 := by ring
      · rw [hak_z k p.1 (lt_of_not_ge fun h => hx (abs_le.mp h))]
        simp [bd]
        exact mul_nonneg (indicator_nonneg (fun _ _ => mul_nonneg hB
          ((abs_nonneg _).trans (hνV 0))) _) (carlesonWeight_nonneg _)
    · filter_upwards [ae_fst_of_ae (ae_tendsto_carlesonMoll ha_i.locallyIntegrable),
        ae_fst_of_ae (ae_tendsto_carlesonMoll hν'_i.locallyIntegrable),
        ae_sub_of_ae (ae_tendsto_carlesonMoll hg_i.locallyIntegrable)] with p h₁ h₂ h₃
      refine ((((Complex.continuous_ofReal.tendsto _).comp h₁).pow 2).mul h₃).mul
        ((Complex.continuous_ofReal.tendsto _).comp ?_)
      exact (tendsto_const_nhds.mul ((Real.continuous_sin.tendsto _).comp
        (h₂.mul_const p.2))).div_const p.2
  have hform' : carlesonForm a ν' g = carlesonForm a ν g := by
    unfold carlesonForm
    congr 1
    ext p
    by_cases hx : p.1 ∈ F
    · simp [ν', indicator_of_mem (hFR hx)]
    · simp [a, hx]
  have hR := ((tendsto_const_nhds (x := C)).mul (((hI.const_mul (2 * 2)).rpow_const
    (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 3))))).mul (tendsto_const_nhds (x := B * Vb ^ (1 / 3 : ℝ)))
    |>.mul ((hI.const_mul (2 * 9)).rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 3)))
  have hlim := le_of_tendsto_of_tendsto' hform.norm hR hk
  rw [hform'] at hlim
  refine hlim.trans_eq ?_
  have hv₃ : v ^ (1 / 3 : ℝ) * v ^ (1 / 3 : ℝ) = v ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add' hv (by norm_num)]
    norm_num
  rw [Real.mul_rpow (by norm_num) hv, Real.mul_rpow (by norm_num) hv, ← hv₃]
  norm_num
  ring
end Auto
