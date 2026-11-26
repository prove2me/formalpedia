-- Prove2me | solution 1 for Auto.aux_pairwise_square_le_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:17.892896+00:00
-- url     : https://prove2.me/submissions/f9c04a27-009e-4878-a919-22f6a0231a56

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_square_endpoint_le_lintegral
public import Theorems.Thm_Auto_aux_same_sign_square_le
public import Theorems.Thm_Auto_aux_cross_square_le
public import Theorems.Thm_Auto_aux_lintegral_Icc_eq_Ioc

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {α β x y : ℝ} (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (hxy : x ≤ y) :
    ‖a y - a x‖ₑ ^ (2 : ℕ) ≤
      8 * ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖deriv a z‖ₑ := by
  let F : ℝ → ℝ≥0∞ := fun z ↦ (2 : ℝ≥0∞) * ‖a z‖ₑ * ‖deriv a z‖ₑ
  by_cases hsign : 0 ≤ a x * a y
  · calc
      ‖a y - a x‖ₑ ^ (2 : ℕ) ≤ ‖a y * a y - a x * a x‖ₑ :=
        aux_same_sign_square_le (a y) (a x) (by simpa [mul_comm] using hsign)
      _ ≤ ∫⁻ z in Set.Icc x y, F z := aux_square_endpoint_le_lintegral a ha hx hy hxy
      _ = ∫⁻ z in Set.Ioc x y, F z := aux_lintegral_Icc_eq_Ioc F x y
      _ ≤ 8 * ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖deriv a z‖ₑ := by
        simp only [F]
        calc
          (∫⁻ z in Set.Ioc x y, 2 * ‖a z‖ₑ * ‖deriv a z‖ₑ) ≤
              ∫⁻ z in Set.Ioc x y, 8 * (‖a z‖ₑ * ‖deriv a z‖ₑ) := by
                apply lintegral_mono
                intro z
                calc
                  2 * ‖a z‖ₑ * ‖deriv a z‖ₑ =
                      2 * (‖a z‖ₑ * ‖deriv a z‖ₑ) := by ring
                  _ ≤ 8 * (‖a z‖ₑ * ‖deriv a z‖ₑ) := by gcongr; norm_num
          _ = 8 * ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖deriv a z‖ₑ :=
            lintegral_const_mul' 8 _ (by norm_num)
  · have hcross : a x * a y < 0 := lt_of_not_ge hsign
    have hzero : (0 : ℝ) ∈ Set.uIcc (a x) (a y) := by
      rw [mem_uIcc]
      rcases (mul_neg_iff.mp hcross) with ⟨hxp, hyn⟩ | ⟨hxn, hyp⟩
      · exact Or.inr ⟨hyn.le, hxp.le⟩
      · exact Or.inl ⟨hxn.le, hyp.le⟩
    have hcont : ContinuousOn a (Set.uIcc x y) := by
      simpa [uIcc_of_le hxy] using ha.continuousOn.mono (Icc_subset_Icc hx.1 hy.2)
    rcases intermediate_value_uIcc hcont hzero with ⟨z, hz, hz0⟩
    have hzIcc : z ∈ Set.Icc x y := by simpa [uIcc_of_le hxy] using hz
    have hzαβ : z ∈ Set.Icc α β :=
      ⟨hx.1.trans hzIcc.1, hzIcc.2.trans hy.2⟩
    have hxz := aux_square_endpoint_le_lintegral a ha hx hzαβ hzIcc.1
    have hzy := aux_square_endpoint_le_lintegral a ha hzαβ hy hzIcc.2
    have hxz' : ‖a x * a x - a z * a z‖ₑ ≤ ∫⁻ q in Set.Icc x z, F q := by
      simpa [F, enorm_sub_rev] using hxz
    have hcross' : ‖a y - a x‖ₑ ^ (2 : ℕ) ≤
        2 * (‖a x * a x - a z * a z‖ₑ + ‖a y * a y - a z * a z‖ₑ) := by
      rw [hz0]
      simpa [add_comm] using aux_cross_square_le (a y) (a x)
    calc
      ‖a y - a x‖ₑ ^ (2 : ℕ) ≤
          2 * (‖a x * a x - a z * a z‖ₑ + ‖a y * a y - a z * a z‖ₑ) := hcross'
      _ ≤ 2 * ((∫⁻ q in Set.Icc x z, F q) + ∫⁻ q in Set.Icc z y, F q) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hxz' hzy) (by norm_num)
      _ = 2 * ((∫⁻ q in Set.Ioc x z, F q) + ∫⁻ q in Set.Ioc z y, F q) := by
        rw [aux_lintegral_Icc_eq_Ioc F x z, aux_lintegral_Icc_eq_Ioc F z y]
      _ = 2 * ∫⁻ q in Set.Ioc x y, F q := by
        rw [← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
          Set.Ioc_union_Ioc_eq_Ioc hzIcc.1 hzIcc.2]
      _ ≤ 8 * ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖deriv a z‖ₑ := by
        simp only [F]
        calc
          2 * (∫⁻ q in Set.Ioc x y, 2 * ‖a q‖ₑ * ‖deriv a q‖ₑ) =
              4 * ∫⁻ q in Set.Ioc x y, ‖a q‖ₑ * ‖deriv a q‖ₑ := by
            rw [show (fun q ↦ 2 * ‖a q‖ₑ * ‖deriv a q‖ₑ) =
              fun q ↦ 2 * (‖a q‖ₑ * ‖deriv a q‖ₑ) by
                funext q
                ring]
            rw [lintegral_const_mul' 2 _ (by norm_num)]
            ring
          _ ≤ 8 * ∫⁻ q in Set.Ioc x y, ‖a q‖ₑ * ‖deriv a q‖ₑ := by
            gcongr; norm_num
end Auto
