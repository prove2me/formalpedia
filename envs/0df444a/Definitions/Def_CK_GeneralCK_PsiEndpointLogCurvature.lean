-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointLogCurvature
-- name    : CK_GeneralCK_PsiEndpointLogCurvature
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T05:14:14.560989+00:00
-- url     : https://prove2.me/theorems/66366da2-387c-4d6f-9565-fb769abe85b4
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointLogCurvature` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointLogCurvature` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointLogCurvature` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointLogCurvature (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointLogCurvature.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointLogGain

-- ===== source module GeneralCK.PsiEndpointLogCurvature =====
section

/-!+# Quantitative curvature of the inverse-entropy logit

An elementary polynomial comparison supplies the logarithmic compensation
on the entire interval required by endpoint contacts of ratio at least eight.
-/

namespace GeneralCK.PsiEndpointLogGain
open Set

private theorem quarter_entropy_inverse {h : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 4) :
    entropyInverse h ≤ 1 / 16 := by
  have hlog : Real.log ((1 / 16 : ℝ)⁻¹) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hc : 0 ≤ Real.log ((1 - (1 / 16 : ℝ))⁻¹) :=
    Real.log_nonneg (by norm_num)
  have hb : (1 / 4 : ℝ) ≤ H (1 / 16) := by
    unfold H Real.binEntropy
    rw [hlog]
    apply (le_div_iff₀ log_two_pos).mpr
    nlinarith
  have hm := entropyInverse_mono hh.le (H_le_one (1 / 16)) (hhi.trans hb)
  rwa [entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num)] at hm

private theorem log_fifteen_lower : (5 / 2 : ℝ) ≤ Real.log 15 := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 15 / 8)
  have he : Real.log 15 = 3 * Real.log 2 + Real.log (15 / 8) := by
    rw [Real.log_div (by norm_num : (15 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0),
      show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    ring
  have hL := Certificates.PilotData.log_two.1
  norm_num only [div_one] at hL
  rw [he]
  norm_num at hh
  linarith

private theorem logit_product_le_one {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    v * Real.log ((1 - v) / v) ≤ 1 := by
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1 - v) hv)) hv.le
  have he : v * ((1 - v) / v - 1) = 1 - 2 * v := by field_simp; ring
  rw [he] at hh
  linarith

private theorem curvature_polynomial {v l : ℝ} (hv : 0 < v)
    (hvi : v ≤ 1 / 16) (hl : 5 / 2 ≤ l) (hvl : v * l ≤ 1) :
    (1 - v) ^ 2 * l ^ 3 ≤ ((1 - 2 * v) * l - 1) * (l + 1) ^ 2 := by
  have hv2l : v ^ 2 * l ≤ v := by nlinarith [mul_le_mul_of_nonneg_left hvl hv.le]
  have hcoef : 11 / 16 ≤ 1 - 4 * v - v ^ 2 * l := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg l)
  have hlin : (1 + 2 * v) * l ≤ (9 / 8) * l :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hquad : 0 ≤ (11 / 16) * l ^ 2 - (9 / 8) * l - 1 := by nlinarith
  nlinarith only [hmul, hlin, hquad]

/-- Logarithmic curvature of `J o entropyInverse`, with the entire
ratio-eight range certified by elementary inequalities. -/
theorem curvature_lower {h : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 4) :
    1 / (Real.log 2 * h ^ 2) ≤ curvature h := by
  let v := entropyInverse h
  let l := Real.log ((1 - v) / v)
  have hv : 0 < v := entropyInverse_pos hh (by linarith)
  have hvi : v ≤ 1 / 16 := quarter_entropy_inverse hh hhi
  have hv1 : v < 1 := by linarith
  have hl : 5 / 2 ≤ l := by
    have hr : (15 : ℝ) ≤ (1 - v) / v := (le_div_iff₀ hv).mpr (by linarith)
    exact log_fifteen_lower.trans (Real.log_le_log (by norm_num) hr)
  have hvl := logit_product_le_one hv hv1
  have hp := curvature_polynomial hv hvi hl hvl
  have hn := PsiExtendedEntropyCurvature.entropy_natural_lower hv hv1
  have he : H v = h := (entropyInverse_spec hh.le (by linarith)).2.2
  rw [he] at hn
  have hsq : (v * (l + 1)) ^ 2 ≤ (h * Real.log 2) ^ 2 := by
    have hb : 0 ≤ v * (l + 1) := by positivity
    nlinarith only [hn, hb]
  have hN : 0 ≤ (1 - 2 * v) * l - 1 := by
    have hb := mul_le_mul (show (7 / 8 : ℝ) ≤ 1 - 2 * v by linarith) hl
      (by norm_num : (0 : ℝ) ≤ 5 / 2) (by linarith : 0 ≤ 1 - 2 * v)
    nlinarith
  have hs := mul_le_mul_of_nonneg_right hsq hN
  have hp' := mul_le_mul_of_nonneg_left hp (sq_nonneg v)
  change 1 / (Real.log 2 * h ^ 2) ≤
    Real.log 2 * ((1 - 2 * v) * l - 1) / (v ^ 2 * (1 - v) ^ 2 * l ^ 3)
  apply (div_le_div_iff₀ (by positivity)
    (by positivity : 0 < v ^ 2 * (1 - v) ^ 2 * l ^ 3)).mpr
  nlinarith only [hs, hp']

theorem Q_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) : Q b ≤ Q a := by
  exact J_antitone (entropyInverse_pos ha (hab.trans hb))
    (entropyInverse_spec (ha.le.trans hab) hb).2.1
    (entropyInverse_mono ha.le hb hab)

noncomputable def compensated (h : ℝ) : ℝ := Q h + Real.log h / Real.log 2

theorem hasDerivAt_compensated {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt compensated (slope h + (1 / Real.log 2) / h) h := by
  convert! (hasDerivAt_Q hh hh1).add ((Real.hasDerivAt_log hh.ne').div_const (Real.log 2)) using 1
  ring

private theorem hasDerivAt_compensated_slope {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (fun x => slope x + (1 / Real.log 2) / x)
      (curvature h - 1 / (Real.log 2 * h ^ 2)) h := by
  convert! (hasDerivAt_slope hh hh1).add
    ((hasDerivAt_const h (1 / Real.log 2)).div (hasDerivAt_id h) hh.ne') using 1
  dsimp
  ring

theorem compensated_convexOn : ConvexOn ℝ (Ioc 0 (1 / 4)) compensated := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc 0 (1 / 4))
    (f' := fun h => slope h + (1 / Real.log 2) / h)
    (f'' := fun h => curvature h - 1 / (Real.log 2 * h ^ 2))
  · intro h hh
    exact (hasDerivAt_compensated hh.1 (by linarith [hh.2])).continuousAt.continuousWithinAt
  · intro h hh
    have hi := interior_subset hh
    exact (hasDerivAt_compensated hi.1 (by linarith [hi.2])).hasDerivWithinAt
  · intro h hh
    have hi := interior_subset hh
    exact (hasDerivAt_compensated_slope hi.1 (by linarith [hi.2])).hasDerivWithinAt
  · intro h hh
    have hi := interior_subset hh
    exact sub_nonneg.mpr (curvature_lower hi.1 hi.2)

/-- The endpoint log gain is uniform over every positive entropy split. -/
theorem Q_split_gain {h t : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 8) (ht : |t| < 1) :
    Q h + PsiSignedSplit.barrier t / (2 * Real.log 2) ≤
      (Q (h * (1 + t)) + Q (h * (1 - t))) / 2 := by
  have hi := abs_lt.mp ht
  have hp : 0 < h * (1 + t) := mul_pos hh (by linarith)
  have hm : 0 < h * (1 - t) := mul_pos hh (by linarith)
  have hpu : h * (1 + t) ≤ 1 / 4 := by nlinarith
  have hmu : h * (1 - t) ≤ 1 / 4 := by nlinarith
  have hj := compensated_convexOn.2 ⟨hp, hpu⟩ ⟨hm, hmu⟩
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hj
  rw [show (1 / 2 : ℝ) * (h * (1 + t)) + (1 / 2) * (h * (1 - t)) = h by ring] at hj
  unfold compensated at hj
  rw [Real.log_mul hh.ne' (by linarith : 1 + t ≠ 0),
    Real.log_mul hh.ne' (by linarith : 1 - t ≠ 0)] at hj
  unfold PsiSignedSplit.barrier
  rw [PsiSignedSplit.log_one_sub_sq ht]
  linear_combination hj

end GeneralCK.PsiEndpointLogGain

#print axioms GeneralCK.PsiEndpointLogGain.curvature_lower
#print axioms GeneralCK.PsiEndpointLogGain.Q_split_gain

end


