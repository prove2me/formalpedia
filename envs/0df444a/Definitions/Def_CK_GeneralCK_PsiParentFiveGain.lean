-- Prove2me | Definitions.Def_CK_GeneralCK_PsiParentFiveGain
-- name    : CK_GeneralCK_PsiParentFiveGain
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:08:30.526455+00:00
-- url     : https://prove2.me/theorems/ac6147a2-1f41-46bd-bf62-94beba2dfc07
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiParentFiveGain` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiParentFiveGain` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiParentFiveGain` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiParentFiveGain (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiParentFiveGain.lean)

import Definitions.Def_CK_GeneralCK_PsiFifthBiasClosure

-- ===== source module GeneralCK.PsiParentFiveGain =====
section

/-! A stronger local parent gain, anchored in the proved eta curvature. -/

namespace GeneralCK.PsiParentFiveGain
open Set PsiExtendedEntropyCurvature

theorem anchor_entropy_bounds :
    (13 / 200 : ℝ) ≤ H (1 / 128) ∧ H (1 / 128) ≤ 11 / 100 ∧
    1 / 22 ≤ Real.log 2 * H (1 / 128) := by
  have hLlo : (69 / 100 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hLhi : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hlog : Real.log ((1 / 128 : ℝ)⁻¹) = 7 * Real.log 2 := by
    norm_num
    rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hu := (PsiOuterEntropy2048.entropy_logit_upper
    (p := (1 / 128 : ℝ)) (n := 7) (by norm_num) (by norm_num) hlog.le).1
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 127 / 128)
  have he : Real.log 2 * H (1 / 128) =
      (7 / 128) * Real.log 2 - (127 / 128) * Real.log (127 / 128) := by
    unfold H Real.binEntropy
    rw [mul_div_cancel₀ _ log_two_pos.ne', hlog]
    norm_num
    rw [show (128 / 127 : ℝ) = (127 / 128)⁻¹ by norm_num, Real.log_inv]
    ring
  have hn : (7 / 128) * Real.log 2 + 127 / 16384 ≤ Real.log 2 * H (1 / 128) := by
    rw [he]
    linarith only [hl]
  refine ⟨?_, by linarith only [hu], ?_⟩
  · apply (mul_le_mul_iff_left₀ log_two_pos).mp
    nlinarith only [hn, hLhi]
  · linarith only [hn, hLlo]

theorem anchor_compensated_slope :
    deriv eta (H (1 / 128)) + 1 / (Real.log 2 * H (1 / 128)) ≤ -5 := by
  have hHpos : 0 < H (1 / 128) := H_pos (by norm_num) (by norm_num)
  have hHlt : H (1 / 128) < 1 := by linarith [anchor_entropy_bounds.2.1]
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hlog : Real.log ((1 / 128 : ℝ)⁻¹) = 7 * Real.log 2 := by
    norm_num
    rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hJ := (PsiOuterEntropy2048.entropy_logit_upper
    (p := (1 / 128 : ℝ)) (n := 7) (by norm_num) (by norm_num) hlog.le).2
  have hJpos : 0 < J (1 / 128) := J_pos (by norm_num) (by norm_num)
  have hdpos : 0 < Real.log 2 * (1 / 128) * (1 - 1 / 128) * J (1 / 128) := by positivity
  have hprod := mul_le_mul hL hJ hJpos.le (by norm_num : (0 : ℝ) ≤ 7 / 10)
  have hquot : (25 : ℝ) ≤ (1 - 2 * (1 / 128)) /
      (Real.log 2 * (1 / 128) * (1 - 1 / 128) * J (1 / 128)) := by
    apply (le_div_iff₀ hdpos).mpr
    nlinarith only [hprod]
  have hinv : 1 / (Real.log 2 * H (1 / 128)) ≤ (22 : ℝ) := by
    apply (div_le_iff₀ (mul_pos log_two_pos hHpos)).mpr
    linarith only [anchor_entropy_bounds.2.2]
  rw [deriv_eta hHpos hHlt,
    entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 1 / 128) (by norm_num)]
  linarith only [hquot, hinv]

theorem neg_deriv_eta_ge_five_logarithmic {h : ℝ}
    (hh : 0 < h) (hcap : h ≤ 13 / 200) :
    5 + 1 / (Real.log 2 * h) ≤ -deriv eta h := by
  have hc := (compensated_convexOn (r := 0) (by norm_num)).monotoneOn_deriv
    (fun x hx => (hasDerivAt_compensated (r := 0) (by norm_num) hx.1
      (by linarith [hx.2])).differentiableAt)
  have ha := anchor_entropy_bounds
  have hhH : h ≤ H (1 / 128) := hcap.trans ha.1
  have hp : 0 < H (1 / 128) := H_pos (by norm_num) (by norm_num)
  have hm := hc (show h ∈ Ioc 0 (11 / 100) from ⟨hh, by linarith⟩)
    (show H (1 / 128) ∈ Ioc 0 (11 / 100) from ⟨hp, ha.2.1⟩) hhH
  rw [(hasDerivAt_compensated (r := 0) (by norm_num) hh (by linarith)).deriv,
    (hasDerivAt_compensated (r := 0) (by norm_num) hp (by linarith [ha.2.1])).deriv,
    EntropyCurvature.radialPhi_zero] at hm
  simp only [compensation, mul_zero, zero_div, sub_zero, div_div] at hm
  linarith only [hm, anchor_compensated_slope]

theorem eta_add_five_linear_log_antitone :
    AntitoneOn (fun h : ℝ => eta h + 5 * h + Real.log h / Real.log 2) (Ioc 0 (13 / 200)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 (13 / 200))
    (f' := fun h => deriv eta h + 5 + 1 / (Real.log 2 * h))
  · apply ContinuousOn.add
    · exact (Scalar.eta_continuousOn.mono (by intro h hh; exact ⟨hh.1, by linarith [hh.2]⟩)).add
        (continuous_const.mul continuous_id).continuousOn
    · exact (Real.continuousOn_log.mono (by intro h hh; exact ne_of_gt hh.1)).div_const _
  · intro h hh
    have hi : h ∈ Ioo (0 : ℝ) (13 / 200) := by simpa only [interior_Ioc] using hh
    have hd := ((hasDerivAt_eta hi.1 (by linarith [hi.2])).add
      ((hasDerivAt_id h).const_mul 5)).add ((Real.hasDerivAt_log hi.1.ne').div_const (Real.log 2))
    rw [← (hasDerivAt_eta hi.1 (by linarith [hi.2])).deriv] at hd
    convert! hd.hasDerivWithinAt using 1
    field_simp
  · intro h hh
    have hi : h ∈ Ioo (0 : ℝ) (13 / 200) := by simpa only [interior_Ioc] using hh
    linarith [neg_deriv_eta_ge_five_logarithmic hi.1 hi.2.le]

theorem eta_increment_ge_five_linear_log {a c : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hac : a + c ≤ 13 / 200) :
    5 * c + Real.log (1 + c / a) / Real.log 2 ≤ eta a - eta (a + c) := by
  have hb : 0 < a + c := by linarith
  have hm := eta_add_five_linear_log_antitone
    (show a ∈ Ioc (0 : ℝ) (13 / 200) from ⟨ha, by linarith⟩)
    (show a + c ∈ Ioc (0 : ℝ) (13 / 200) from ⟨hb, hac⟩) (by linarith)
  have he : 1 + c / a = (a + c) / a := by field_simp
  rw [he, Real.log_div hb.ne' ha.ne', sub_div]
  linarith

end GeneralCK.PsiParentFiveGain

#print axioms GeneralCK.PsiParentFiveGain.anchor_entropy_bounds
#print axioms GeneralCK.PsiParentFiveGain.anchor_compensated_slope
#print axioms GeneralCK.PsiParentFiveGain.neg_deriv_eta_ge_five_logarithmic
#print axioms GeneralCK.PsiParentFiveGain.eta_add_five_linear_log_antitone
#print axioms GeneralCK.PsiParentFiveGain.eta_increment_ge_five_linear_log

end


