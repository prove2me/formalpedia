-- Prove2me | Definitions.Def_CK_GeneralCK_PsiParentFiveGainExtended
-- name    : CK_GeneralCK_PsiParentFiveGainExtended
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:27:30.101931+00:00
-- url     : https://prove2.me/theorems/062ce0e9-f9e8-4d45-958d-88aeaff5dd73
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiParentFiveGainExtended` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiParentFiveGainExtended` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiParentFiveGainExtended` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiParentFiveGainExtended (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiParentFiveGainExtended.lean)

import Definitions.Def_CK_GeneralCK_PsiQuarterBiasClosure

-- ===== source module GeneralCK.PsiParentFiveGainExtended =====
section

/-! The five-linear parent gain through entropy 77/800. -/

namespace GeneralCK.PsiParentFiveGainExtended
open Set PsiExtendedEntropyCurvature

theorem anchor_entropy_bounds :
    (77 / 800 : ℝ) ≤ H (1 / 80) ∧ H (1 / 80) ≤ 11 / 100 ∧
    1 / 15 ≤ Real.log 2 * H (1 / 80) := by
  have hLlo : (69 / 100 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hLhi : Real.log 2 ≤ (25 / 36 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hloglo := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)
  norm_num at hloglo
  have he80 : Real.log (80 : ℝ) = 6 * Real.log 2 + Real.log (5 / 4) := by
    rw [show (80 : ℝ) = 2 ^ (6 : ℕ) * (5 / 4) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ^ (6 : ℕ) ≠ 0)
        (by norm_num : (5 / 4 : ℝ) ≠ 0), Real.log_pow]
    norm_num
  have hloghi : Real.log ((1 / 80 : ℝ)⁻¹) ≤ 7 * Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 80)
      (show (80 : ℝ) ≤ 2 ^ (7 : ℕ) by norm_num)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  have hu := (PsiOuterEntropy2048.entropy_logit_upper
    (p := (1 / 80 : ℝ)) (n := 7) (by norm_num) (by norm_num) hloghi).1
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 79 / 80)
  have he : Real.log 2 * H (1 / 80) =
      (1 / 80) * Real.log 80 - (79 / 80) * Real.log (79 / 80) := by
    unfold H Real.binEntropy
    rw [mul_div_cancel₀ _ log_two_pos.ne']
    norm_num
    rw [show (80 / 79 : ℝ) = (79 / 80)⁻¹ by norm_num, Real.log_inv]
    ring
  have hn : (6 / 80) * Real.log 2 + 2 / 720 + 79 / 6400 ≤ Real.log 2 * H (1 / 80) := by
    rw [he, he80]
    linarith only [hl, hloglo]
  refine ⟨?_, by linarith only [hu], ?_⟩
  · apply (mul_le_mul_iff_left₀ log_two_pos).mp
    nlinarith only [hn, hLhi]
  · linarith only [hn, hLlo]

theorem anchor_compensated_slope :
    deriv eta (H (1 / 80)) + 1 / (Real.log 2 * H (1 / 80)) ≤ -5 := by
  have hHpos : 0 < H (1 / 80) := H_pos (by norm_num) (by norm_num)
  have hHlt : H (1 / 80) < 1 := by linarith [anchor_entropy_bounds.2.1]
  have hL : Real.log 2 ≤ (25 / 36 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 79 ^ (16 : ℕ))
    (show (79 : ℝ) ^ (16 : ℕ) ≤ 2 ^ (101 : ℕ) by norm_num)
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  have hJ : J (1 / 80) ≤ (101 / 16 : ℝ) := by
    unfold J
    norm_num
    apply (div_le_iff₀ log_two_pos).mpr
    linarith only [hlog]
  have hJpos : 0 < J (1 / 80) := J_pos (by norm_num) (by norm_num)
  have hdpos : 0 < Real.log 2 * (1 / 80) * (1 - 1 / 80) * J (1 / 80) := by positivity
  have hprod := mul_le_mul hL hJ hJpos.le (by norm_num : (0 : ℝ) ≤ 25 / 36)
  have hquot : (18 : ℝ) ≤ (1 - 2 * (1 / 80)) /
      (Real.log 2 * (1 / 80) * (1 - 1 / 80) * J (1 / 80)) := by
    apply (le_div_iff₀ hdpos).mpr
    nlinarith only [hprod]
  have hinv : 1 / (Real.log 2 * H (1 / 80)) ≤ (15 : ℝ) := by
    apply (div_le_iff₀ (mul_pos log_two_pos hHpos)).mpr
    linarith only [anchor_entropy_bounds.2.2]
  rw [deriv_eta hHpos hHlt,
    entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 1 / 80) (by norm_num)]
  linarith only [hquot, hinv]

theorem neg_deriv_eta_ge_five_logarithmic {h : ℝ}
    (hh : 0 < h) (hcap : h ≤ 77 / 800) :
    5 + 1 / (Real.log 2 * h) ≤ -deriv eta h := by
  have hc := (compensated_convexOn (r := 0) (by norm_num)).monotoneOn_deriv
    (fun x hx => (hasDerivAt_compensated (r := 0) (by norm_num) hx.1
      (by linarith [hx.2])).differentiableAt)
  have ha := anchor_entropy_bounds
  have hhH : h ≤ H (1 / 80) := hcap.trans ha.1
  have hp : 0 < H (1 / 80) := H_pos (by norm_num) (by norm_num)
  have hm := hc (show h ∈ Ioc 0 (11 / 100) from ⟨hh, by linarith⟩)
    (show H (1 / 80) ∈ Ioc 0 (11 / 100) from ⟨hp, ha.2.1⟩) hhH
  rw [(hasDerivAt_compensated (r := 0) (by norm_num) hh (by linarith)).deriv,
    (hasDerivAt_compensated (r := 0) (by norm_num) hp (by linarith [ha.2.1])).deriv,
    EntropyCurvature.radialPhi_zero] at hm
  simp only [compensation, mul_zero, zero_div, sub_zero, div_div] at hm
  linarith only [hm, anchor_compensated_slope]

theorem eta_add_five_linear_log_antitone :
    AntitoneOn (fun h : ℝ => eta h + 5 * h + Real.log h / Real.log 2) (Ioc 0 (77 / 800)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 (77 / 800))
    (f' := fun h => deriv eta h + 5 + 1 / (Real.log 2 * h))
  · apply ContinuousOn.add
    · exact (Scalar.eta_continuousOn.mono (by intro h hh; exact ⟨hh.1, by linarith [hh.2]⟩)).add
        (continuous_const.mul continuous_id).continuousOn
    · exact (Real.continuousOn_log.mono (by intro h hh; exact ne_of_gt hh.1)).div_const _
  · intro h hh
    have hi : h ∈ Ioo (0 : ℝ) (77 / 800) := by simpa only [interior_Ioc] using hh
    have hd := ((hasDerivAt_eta hi.1 (by linarith [hi.2])).add
      ((hasDerivAt_id h).const_mul 5)).add ((Real.hasDerivAt_log hi.1.ne').div_const (Real.log 2))
    rw [← (hasDerivAt_eta hi.1 (by linarith [hi.2])).deriv] at hd
    convert! hd.hasDerivWithinAt using 1
    field_simp
  · intro h hh
    have hi : h ∈ Ioo (0 : ℝ) (77 / 800) := by simpa only [interior_Ioc] using hh
    linarith [neg_deriv_eta_ge_five_logarithmic hi.1 hi.2.le]

theorem eta_increment_ge_five_linear_log {a c : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hac : a + c ≤ 77 / 800) :
    5 * c + Real.log (1 + c / a) / Real.log 2 ≤ eta a - eta (a + c) := by
  have hb : 0 < a + c := by linarith
  have hm := eta_add_five_linear_log_antitone
    (show a ∈ Ioc (0 : ℝ) (77 / 800) from ⟨ha, by linarith⟩)
    (show a + c ∈ Ioc (0 : ℝ) (77 / 800) from ⟨hb, hac⟩) (by linarith)
  have he : 1 + c / a = (a + c) / a := by field_simp
  rw [he, Real.log_div hb.ne' ha.ne', sub_div]
  linarith

end GeneralCK.PsiParentFiveGainExtended

#print axioms GeneralCK.PsiParentFiveGainExtended.anchor_entropy_bounds
#print axioms GeneralCK.PsiParentFiveGainExtended.anchor_compensated_slope
#print axioms GeneralCK.PsiParentFiveGainExtended.neg_deriv_eta_ge_five_logarithmic
#print axioms GeneralCK.PsiParentFiveGainExtended.eta_add_five_linear_log_antitone
#print axioms GeneralCK.PsiParentFiveGainExtended.eta_increment_ge_five_linear_log

end


