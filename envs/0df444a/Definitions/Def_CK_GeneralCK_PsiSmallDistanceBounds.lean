-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSmallDistanceBounds
-- name    : CK_GeneralCK_PsiSmallDistanceBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:56:46.688487+00:00
-- url     : https://prove2.me/theorems/e3a5a08c-4587-486e-ad14-96ca860835cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSmallDistanceBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSmallDistanceBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSmallDistanceBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSmallDistanceBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSmallDistanceBounds.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneSymmetric
import Definitions.Def_CK_GeneralCK_PsiParentEntropyGain
import Definitions.Def_CK_GeneralCK_EntropyParabola
import Definitions.Def_CK_GeneralCK_RadialConcavity

-- ===== source module GeneralCK.PsiSmallDistanceBounds =====
section

namespace GeneralCK.PsiSmallDistance
open Set

theorem log_five_ratio_lower : (58 / 25 : ℝ) * Real.log 2 ≤ Real.log 5 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ (58 : ℕ))
    (by norm_num : (2 : ℝ) ^ (58 : ℕ) ≤ 5 ^ (25 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem contact_four_upper : radialContact 4 1 ≤ (1 : ℝ) / 26 := by
  apply (radialContact_le_iff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).2
  have hlog : (116 / 25 : ℝ) * Real.log 2 ≤ Real.log 26 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 25) (by norm_num : (25 : ℝ) ≤ 26)
    rw [show (25 : ℝ) = 5 ^ (2 : ℕ) by norm_num, Real.log_pow] at h
    norm_num at h
    nlinarith [log_five_ratio_lower]
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 25 / 26)
  have hh : (1 / 26 : ℝ) * Real.log 26 + (1 / 26) * (25 / 26) ≤
      H (1 / 26) * Real.log 2 := by
    rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
    norm_num
    rw [show (26 / 25 : ℝ) = ((25 / 26 : ℝ))⁻¹ by norm_num, Real.log_inv]
    nlinarith only [hc]
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have hl := Certificates.PilotData.log_two.2
    norm_num at hl
    linarith
  have hH : (3 / 13 : ℝ) ≤ H (1 / 26) := by
    nlinarith [log_two_pos]
  norm_num
  linarith

theorem F_four_lower : (464 / 25 : ℝ) ≤ F 4 1 := by
  have hm := J_antitone (radialContact_pos (by norm_num) (by norm_num))
    (by norm_num : (1 : ℝ) / 26 ≤ 1 / 2) contact_four_upper
  have hJ : (116 / 25 : ℝ) ≤ J (1 / 26) := by
    unfold J
    norm_num
    apply (le_div_iff₀ log_two_pos).2
    rw [show (25 : ℝ) = 5 ^ (2 : ℕ) by norm_num, Real.log_pow]
    nlinarith [log_five_ratio_lower]
  simp only [F, show (4 : ℝ) ≠ 0 by norm_num, ↓reduceIte]
  linarith

theorem F_lower_small_ratio {d E : ℝ} (hd : 0 < d) (hE : 0 < E) (hdE : d ≤ 4 * E) :
    (29 / 25) * (d ^ 2 / E) ≤ F d E := by
  have hr : 0 < d / E := div_pos hd hE
  have hr4 : d / E ≤ 4 := (div_le_iff₀ hE).2 (by linarith)
  have h := antitoneOn_F_div_sq (h := 1) (by norm_num)
    hr (by norm_num : (0 : ℝ) < 4) hr4
  have hratio : (29 / 25 : ℝ) ≤ F (d / E) 1 / (d / E) ^ 2 := by
    norm_num at h
    linarith [F_four_lower]
  have hb := (le_div_iff₀ (sq_pos_of_pos hr)).mp hratio
  have hmul := mul_le_mul_of_nonneg_left hb hE.le
  have heq : E * F (d / E) 1 = F d E := by
    simpa only [mul_div_cancel₀ d hE.ne', mul_one] using (F_scale (d / E) 1 E).symm
  rw [heq] at hmul
  convert! hmul using 1 <;> field_simp <;> ring

theorem neg_deriv_eta_small_upper {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 100000) :
    -deriv eta h ≤ (8 / 5) / h := by
  let v := entropyInverse h
  let t := Real.log ((1 - v) / v)
  have hh1 : h < 1 := by linarith
  have hv : 0 < v := entropyInverse_pos hh hh1.le
  have hvhalf : v < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hH : H v = h := (entropyInverse_spec hh.le hh1.le).2.2
  have hvc : 0 < 1 - v := by linarith
  have hvsmall : v ≤ 1 / 65536 := by
    have hp := H_gt_parabola hv hvhalf
    rw [hH] at hp
    have hv2 : 2 * v ≤ h := by nlinarith [mul_pos hv (show 0 < 1 - 2 * v by linarith)]
    linarith
  have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by
    have hl := Certificates.PilotData.log_two.1
    norm_num at hl
    linarith
  have ht : 10 ≤ t := by
    have hratio : (32768 : ℝ) ≤ (1 - v) / v := (le_div_iff₀ hv).2 (by linarith)
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 32768) hratio
    rw [show (32768 : ℝ) = 2 ^ (15 : ℕ) by norm_num, Real.log_pow] at hl
    dsimp [t]
    nlinarith only [hl, hL]
  have htpos : 0 < t := by linarith
  have hlogc : -Real.log (1 - v) ≤ v / (1 - v) := by
    have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hvc)
    rw [Real.log_inv] at hl
    have heq : (1 - v)⁻¹ - 1 = v / (1 - v) := by field_simp; ring
    rwa [heq] at hl
  have hbin : h * Real.log 2 = v * t - Real.log (1 - v) := by
    rw [← hH, H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
    dsimp [t]
    rw [Real.log_div hvc.ne' hv.ne']
    simp only [Real.log_inv]
    ring
  have hvinv : v / (1 - v) ≤ v * (100 / 99) := by
    apply (div_le_iff₀ hvc).2
    nlinarith [mul_nonneg hv.le (show 0 ≤ 1 / 100 - v by linarith)]
  have hcoef : t + 100 / 99 ≤ (1599 / 1000 : ℝ) * Real.log 2 * t := by
    have hl := mul_le_mul_of_nonneg_right hL htpos.le
    nlinarith only [hl, ht]
  have hhvt : h ≤ (1599 / 1000 : ℝ) * v * t := by
    have hb : h * Real.log 2 ≤ v * (t + 100 / 99) := by nlinarith only [hbin, hlogc, hvinv]
    have hc := mul_le_mul_of_nonneg_left hcoef hv.le
    nlinarith [log_two_pos]
  have hden : 0 < v * (1 - v) * t := by positivity
  have hfrac : h * ((1 - 2 * v) / (v * (1 - v) * t)) ≤ 1599 / 1000 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).2
    have ha := mul_le_mul_of_nonneg_right hhvt hvc.le
    have hb := mul_le_mul_of_nonneg_left (show 1 - 2 * v ≤ 1 - v by linarith) hh.le
    nlinarith only [ha, hb]
  have hd : deriv eta h = -2 - (1 - 2 * v) / (v * (1 - v) * t) := by
    rw [deriv_eta hh hh1]
    change -2 - (1 - 2 * v) / (Real.log 2 * v * (1 - v) * J v) = _
    unfold J
    dsimp [t]
    field_simp
  apply (le_div_iff₀ hh).2
  rw [hd]
  nlinarith only [hfrac, hh']

end GeneralCK.PsiSmallDistance

#print axioms GeneralCK.PsiSmallDistance.F_lower_small_ratio
#print axioms GeneralCK.PsiSmallDistance.neg_deriv_eta_small_upper

end


