-- Prove2me | Definitions.Def_CK_GeneralCK_PsiThreeTenthsParentGain
-- name    : CK_GeneralCK_PsiThreeTenthsParentGain
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:53:00.505105+00:00
-- url     : https://prove2.me/theorems/c88a1012-a9c5-4271-af66-ecaaaa114937
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiThreeTenthsParentGain` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiThreeTenthsParentGain` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiThreeTenthsParentGain` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiThreeTenthsParentGain (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiThreeTenthsParentGain.lean)

import Definitions.Def_CK_GeneralCK_PsiTwoSeventhsBiasClosure

-- ===== source module GeneralCK.PsiThreeTenthsParentGain =====
section

/-! The five-linear parent gain through entropy 1041/10000. -/

namespace GeneralCK.PsiThreeTenthsParentGain
open Set PsiExtendedEntropyCurvature

theorem previous_cap_obstruction :
    (77 / 800 : ℝ) < 3 / 80 + (1 - H (7 / 20)) := by
  have hC : 0 ≤ 1 - H (7 / 20) := sub_nonneg.mpr (H_le_one _)
  have hL : Real.log 2 ≤ (25 / 36 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hc := SmallMean.Cn_ge_half_sq (r := (3 / 10 : ℝ)) (by norm_num) (by norm_num)
  norm_num [SmallMean.Cn] at hc
  have hm := mul_le_mul_of_nonneg_right hL hC
  nlinarith only [hc, hm]

theorem anchor_entropy_bounds :
    (1041 / 10000 : ℝ) ≤ H (1 / 73) ∧ H (1 / 73) ≤ 11 / 100 ∧
    50 / 691 ≤ Real.log 2 * H (1 / 73) := by
  have hLlo : (69314 / 100000 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hLhi : Real.log 2 ≤ (69315 / 100000 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hl₁ := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 64)
  have hl₂ := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 72)
  norm_num at hl₁ hl₂
  have he73 : Real.log (73 : ℝ) = 6 * Real.log 2 + Real.log (73 / 64) := by
    rw [show (73 : ℝ) = 2 ^ (6 : ℕ) * (73 / 64) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ^ (6 : ℕ) ≠ 0)
        (by norm_num : (73 / 64 : ℝ) ≠ 0), Real.log_pow]
    norm_num
  have hloghi : Real.log ((1 / 73 : ℝ)⁻¹) ≤ (25 / 4) * Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 73 ^ (4 : ℕ))
      (show (73 : ℝ) ^ (4 : ℕ) ≤ 2 ^ (25 : ℕ) by norm_num)
    rw [Real.log_pow, Real.log_pow] at hh
    norm_num at hh ⊢
    linarith only [hh]
  have hu := (PsiOuterEntropy2048.entropy_logit_upper
    (p := (1 / 73 : ℝ)) (n := 25 / 4) (by norm_num) (by norm_num) hloghi).1
  have he : Real.log 2 * H (1 / 73) =
      (1 / 73) * Real.log 73 + (72 / 73) * Real.log (73 / 72) := by
    unfold H Real.binEntropy
    rw [mul_div_cancel₀ _ log_two_pos.ne']
    norm_num
  have hn : (6 / 73) * Real.log 2 + 18 / (73 * 137) + 144 / (73 * 145) ≤
      Real.log 2 * H (1 / 73) := by
    rw [he, he73]
    linarith only [hl₁, hl₂]
  have hn' : (50 / 691 : ℝ) ≤ Real.log 2 * H (1 / 73) := by
    linarith only [hn, hLlo]
  refine ⟨?_, by linarith only [hu], hn'⟩
  apply (mul_le_mul_iff_left₀ log_two_pos).mp
  nlinarith only [hn', hLhi]

theorem anchor_compensated_slope :
    deriv eta (H (1 / 73)) + 1 / (Real.log 2 * H (1 / 73)) ≤ -5 := by
  have hHpos : 0 < H (1 / 73) := H_pos (by norm_num) (by norm_num)
  have hHlt : H (1 / 73) < 1 := by linarith [anchor_entropy_bounds.2.1]
  have hL : Real.log 2 ≤ (69315 / 100000 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 72 ^ (41 : ℕ))
    (show (72 : ℝ) ^ (41 : ℕ) ≤ 2 ^ (253 : ℕ) by norm_num)
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  have hJ : J (1 / 73) ≤ (253 / 41 : ℝ) := by
    unfold J
    norm_num
    apply (div_le_iff₀ log_two_pos).mpr
    linarith only [hlog]
  have hJpos : 0 < J (1 / 73) := J_pos (by norm_num) (by norm_num)
  have hdpos : 0 < Real.log 2 * (1 / 73) * (1 - 1 / 73) * J (1 / 73) := by positivity
  have hprod := mul_le_mul hL hJ hJpos.le (by norm_num : (0 : ℝ) ≤ 69315 / 100000)
  have hquot : (841 / 50 : ℝ) ≤ (1 - 2 * (1 / 73)) /
      (Real.log 2 * (1 / 73) * (1 - 1 / 73) * J (1 / 73)) := by
    apply (le_div_iff₀ hdpos).mpr
    nlinarith only [hprod]
  have hinv : 1 / (Real.log 2 * H (1 / 73)) ≤ (691 / 50 : ℝ) := by
    apply (div_le_iff₀ (mul_pos log_two_pos hHpos)).mpr
    linarith only [anchor_entropy_bounds.2.2]
  rw [deriv_eta hHpos hHlt,
    entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 1 / 73) (by norm_num)]
  linarith only [hquot, hinv]

theorem neg_deriv_eta_ge_five_logarithmic {h : ℝ}
    (hh : 0 < h) (hcap : h ≤ 1041 / 10000) :
    5 + 1 / (Real.log 2 * h) ≤ -deriv eta h := by
  have hc := (compensated_convexOn (r := 0) (by norm_num)).monotoneOn_deriv
    (fun x hx => (hasDerivAt_compensated (r := 0) (by norm_num) hx.1
      (by linarith [hx.2])).differentiableAt)
  have ha := anchor_entropy_bounds
  have hhH : h ≤ H (1 / 73) := hcap.trans ha.1
  have hp : 0 < H (1 / 73) := H_pos (by norm_num) (by norm_num)
  have hm := hc (show h ∈ Ioc 0 (11 / 100) from ⟨hh, by linarith⟩)
    (show H (1 / 73) ∈ Ioc 0 (11 / 100) from ⟨hp, ha.2.1⟩) hhH
  rw [(hasDerivAt_compensated (r := 0) (by norm_num) hh (by linarith)).deriv,
    (hasDerivAt_compensated (r := 0) (by norm_num) hp (by linarith [ha.2.1])).deriv,
    EntropyCurvature.radialPhi_zero] at hm
  simp only [compensation, mul_zero, zero_div, sub_zero, div_div] at hm
  linarith only [hm, anchor_compensated_slope]

theorem eta_add_five_linear_log_antitone :
    AntitoneOn (fun h : ℝ => eta h + 5 * h + Real.log h / Real.log 2) (Ioc 0 (1041 / 10000)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 (1041 / 10000))
    (f' := fun h => deriv eta h + 5 + 1 / (Real.log 2 * h))
  · apply ContinuousOn.add
    · exact (Scalar.eta_continuousOn.mono (by intro h hh; exact ⟨hh.1, by linarith [hh.2]⟩)).add
        (continuous_const.mul continuous_id).continuousOn
    · exact (Real.continuousOn_log.mono (by intro h hh; exact ne_of_gt hh.1)).div_const _
  · intro h hh
    have hi : h ∈ Ioo (0 : ℝ) (1041 / 10000) := by simpa only [interior_Ioc] using hh
    have hd := ((hasDerivAt_eta hi.1 (by linarith [hi.2])).add
      ((hasDerivAt_id h).const_mul 5)).add ((Real.hasDerivAt_log hi.1.ne').div_const (Real.log 2))
    rw [← (hasDerivAt_eta hi.1 (by linarith [hi.2])).deriv] at hd
    convert! hd.hasDerivWithinAt using 1
    field_simp
  · intro h hh
    have hi : h ∈ Ioo (0 : ℝ) (1041 / 10000) := by simpa only [interior_Ioc] using hh
    linarith [neg_deriv_eta_ge_five_logarithmic hi.1 hi.2.le]

theorem eta_increment_ge_five_linear_log {a c : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hac : a + c ≤ 1041 / 10000) :
    5 * c + Real.log (1 + c / a) / Real.log 2 ≤ eta a - eta (a + c) := by
  have hb : 0 < a + c := by linarith
  have hm := eta_add_five_linear_log_antitone
    (show a ∈ Ioc (0 : ℝ) (1041 / 10000) from ⟨ha, by linarith⟩)
    (show a + c ∈ Ioc (0 : ℝ) (1041 / 10000) from ⟨hb, hac⟩) (by linarith)
  have he : 1 + c / a = (a + c) / a := by field_simp
  rw [he, Real.log_div hb.ne' ha.ne', sub_div]
  linarith

end GeneralCK.PsiThreeTenthsParentGain

#print axioms GeneralCK.PsiThreeTenthsParentGain.previous_cap_obstruction
#print axioms GeneralCK.PsiThreeTenthsParentGain.anchor_entropy_bounds
#print axioms GeneralCK.PsiThreeTenthsParentGain.anchor_compensated_slope
#print axioms GeneralCK.PsiThreeTenthsParentGain.neg_deriv_eta_ge_five_logarithmic
#print axioms GeneralCK.PsiThreeTenthsParentGain.eta_add_five_linear_log_antitone
#print axioms GeneralCK.PsiThreeTenthsParentGain.eta_increment_ge_five_linear_log

end


