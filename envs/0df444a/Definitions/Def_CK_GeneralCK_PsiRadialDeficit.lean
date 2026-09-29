-- Prove2me | Definitions.Def_CK_GeneralCK_PsiRadialDeficit
-- name    : CK_GeneralCK_PsiRadialDeficit
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:14:24.19754+00:00
-- url     : https://prove2.me/theorems/3f7fa0a6-8fc9-408f-8cb7-7f25acaa6aaf
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiRadialDeficit` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiRadialDeficit` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiRadialDeficit` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiRadialDeficit (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiRadialDeficit.lean)

import Definitions.Def_CK_GeneralCK_EntropyRadialDerivatives
import Definitions.Def_CK_GeneralCK_RadialConcavity

-- ===== source module GeneralCK.PsiRadialDeficit =====
section

/-!
# An analytic radial-loss estimate for the normalized active-psi branch

The contact at ratio eight is bracketed by elementary entropy/logarithm
inequalities. Together with the existing decreasing radial-slope ratio this
bounds the radial loss for the entire continuum `d / E >= 8`.
-/

namespace GeneralCK
namespace PsiRadialDeficit
open Set
open Certificates.Mixed Certificates.Mixed.Tails

private theorem entropy_natural_upper {p : ℝ} (_hp : 0 < p) (hp1 : p < 1) :
    H p * Real.log 2 ≤ p * Real.log p⁻¹ + p := by
  have hc : 0 < 1 - p := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hc)
  have hh := mul_le_mul_of_nonneg_left h hc.le
  have he : (1 - p) * ((1 - p)⁻¹ - 1) = p := by field_simp; ring
  rw [he] at hh
  rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
  linarith

private theorem entropy_natural_lower {p : ℝ} (_hp : 0 < p) (hp1 : p < 1) :
    p * Real.log p⁻¹ + p * (1 - p) ≤ H p * Real.log 2 := by
  have hc : 0 < 1 - p := by linarith
  have h := Real.log_le_sub_one_of_pos hc
  have hl : p ≤ Real.log (1 - p)⁻¹ := by rw [Real.log_inv]; linarith
  have hh := mul_le_mul_of_nonneg_left hl hc.le
  rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
  nlinarith

/-- A broad exact bracket suffices; no inverse-entropy interval evaluation
or numerical root enclosure is used. -/
theorem contact_eight_bracket :
    (1 : ℝ) / 64 ≤ radialContact 8 1 ∧ radialContact 8 1 ≤ 1 / 48 := by
  have hL : (2 / 3 : ℝ) < Real.log 2 := by linarith [log_two_gt_69]
  have hL1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  constructor
  · apply (le_radialContact_iff (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).2
    have h := entropy_natural_upper (p := 1 / 64) (by norm_num) (by norm_num)
    have hlog : Real.log ((1 / 64 : ℝ)⁻¹) = 6 * Real.log 2 := by
      norm_num
      rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [hlog] at h
    have hH : H (1 / 64 : ℝ) ≤ 15 / 128 := by
      nlinarith [mul_nonneg log_two_pos.le (sub_nonneg.mpr (H_le_one (1 / 64)))]
    norm_num
    linarith
  · apply (radialContact_le_iff (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).2
    have h := entropy_natural_lower (p := 1 / 48) (by norm_num) (by norm_num)
    have hlog : 5 * Real.log 2 ≤ Real.log ((1 / 48 : ℝ)⁻¹) := by
      have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 32) (by norm_num : (32 : ℝ) ≤ 48)
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow] at hl
      norm_num at hl ⊢
      exact hl
    have hH : (287 / 2304 : ℝ) ≤ H (1 / 48) := by
      have hp := mul_nonneg (sub_nonneg.mpr hL1)
        (H_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 48) (by norm_num))
      nlinarith
    norm_num
    linarith

theorem radial_slope_lt_eight_on_contact_bracket {v : ℝ}
    (hl : 1 / 64 ≤ v) (hu : v ≤ 1 / 48) : radialSlope v < 8 := by
  have hv : 0 < v := by linarith
  have hvh : v < 1 / 2 := by linarith
  have hL : 0 < Real.log 2 := log_two_pos
  have hk := kap_pos hv hvh
  have hc : 0 < 1 - v := by linarith
  have hh0 : 0 ≤ hn v := by
    rw [hn_eq_H_mul_log]
    exact mul_nonneg (H_nonneg hv.le (by linarith)) hL.le
  have hJ : J v < 6 := by
    have hm := J_antitone (by norm_num : (0 : ℝ) < 1 / 64) hvh.le hl
    have ha : J (1 / 64 : ℝ) < 6 := by
      have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 63) (by norm_num : (63 : ℝ) < 64)
      rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow] at h
      unfold J
      norm_num
      apply (div_lt_iff₀ hL).2
      simpa using h
    exact hm.trans_lt ha
  have he : (69 / 20 : ℝ) ≤ logit v := by
    have hr : (32 : ℝ) ≤ (1 - v) / v := (le_div_iff₀ hv).2 (by linarith)
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 32) hr
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow] at hm
    unfold logit
    nlinarith [log_two_gt_69]
  have he0 : 0 < logit v := by linarith
  have hratio := left_ratio_bound hv (show v ≤ 1 / 22 by linarith)
  have hratio' : hn v / ((4 * v * (1 - v)) * kap v) ≤
      (10 / 19 : ℝ) * (1 + (20 / 19) / (69 / 20)) := by
    apply hratio.trans
    gcongr
  have hratio0 : 0 ≤ hn v / ((4 * v * (1 - v)) * kap v) := by positivity
  have hcoef : 2 * (1 - 2 * v) / Real.log 2 ≤ (200 / 69 : ℝ) := by
    apply (div_le_iff₀ hL).2
    nlinarith [log_two_gt_69]
  have hh := mul_le_mul hcoef hratio' hratio0 (by norm_num : (0 : ℝ) ≤ 200 / 69)
  have hid : (2 * (1 - 2 * v) / Real.log 2) *
      (hn v / ((4 * v * (1 - v)) * kap v)) =
      (1 - 2 * v) * hn v / (2 * Real.log 2 * v * (1 - v) * kap v) := by
    field_simp
    ring
  rw [hid] at hh
  have hcorrection : (1 - 2 * v) * hn v /
      (2 * Real.log 2 * v * (1 - v) * kap v) < 2 :=
    hh.trans_lt (by norm_num)
  unfold radialSlope
  linarith

theorem deriv_F_eight_lt_eight : deriv (fun r => F r 1) 8 < 8 := by
  rw [deriv_F_radius_slope (by norm_num) (by norm_num)]
  exact radial_slope_lt_eight_on_contact_bracket contact_eight_bracket.1 contact_eight_bracket.2

theorem radial_ratio_le_half {x : ℝ} (hx : 8 ≤ x) :
    deriv (fun r => F r 1) x / (2 * x) ≤ 1 / 2 := by
  have hm := antitoneOn_F_radius_ratio (by norm_num : (0 : ℝ) < 1)
    (show (8 : ℝ) ∈ Ioi 0 by norm_num) (show x ∈ Ioi 0 by change 0 < x; linarith) hx
  have he : deriv (fun r => F r 1) 8 / (2 * 8) ≤ 1 / 2 := by
    have hd := deriv_F_eight_lt_eight
    norm_num
    linarith
  exact hm.trans he

/-- Uniform radial averaging loss, including displaced radii crossing zero.
The bound requires no entropy upper cutoff. -/
theorem radial_average_loss_le_half {d E : ℝ}
    (hE : 0 < E) (hd : 8 * E ≤ d) (q : ℝ) :
    (F |d - q| E + F |d + q| E) / 2 - F d E ≤ q^2 / (2 * E) := by
  have hd0 : 0 < d := by linarith
  have hx : 8 ≤ d / E := (le_div_iff₀ hE).2 hd
  have hb := radial_ratio_le_half hx
  have hh := F_average_difference_le hd0 hE q
  have heq : q^2 / (2 * d) * deriv (fun r => F r E) d =
      (q^2 / E) * (deriv (fun r => F r 1) (d / E) / (2 * (d / E))) := by
    rw [deriv_F_radius_normalize hd0 hE]
    field_simp
  have hp := mul_le_mul_of_nonneg_left hb (show 0 ≤ q^2 / E by positivity)
  rw [heq] at hh
  calc
    _ ≤ (q^2 / E) * (deriv (fun r => F r 1) (d / E) / (2 * (d / E))) := hh
    _ ≤ (q^2 / E) * (1 / 2) := hp
    _ = q^2 / (2 * E) := by ring

#print axioms contact_eight_bracket
#print axioms radial_slope_lt_eight_on_contact_bracket
#print axioms deriv_F_eight_lt_eight
#print axioms radial_ratio_le_half
#print axioms radial_average_loss_le_half

end PsiRadialDeficit
end GeneralCK

end


