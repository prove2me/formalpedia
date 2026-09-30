-- Prove2me | Definitions.Def_CK_GeneralCK_PsiParentElevenHalvesGain
-- name    : CK_GeneralCK_PsiParentElevenHalvesGain
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:13:32.209448+00:00
-- url     : https://prove2.me/theorems/07edca6a-3e93-4cba-aaf3-a40ebff6308c
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiParentElevenHalvesGain` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiParentElevenHalvesGain` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiParentElevenHalvesGain` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiParentElevenHalvesGain (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiParentElevenHalvesGain.lean)

import Definitions.Def_CK_GeneralCK_PsiFifthBiasAutomaticClosure

-- ===== source module GeneralCK.PsiParentElevenHalvesGain =====
section

/-! A stronger parent slope anchor through entropy two twenty-fifths. -/

namespace GeneralCK.PsiParentElevenHalvesGain
open Set PsiExtendedEntropyCurvature

theorem log_hundred_bounds :
    6 * Real.log 2 + 4 / 9 ≤ Real.log 100 ∧ Real.log 100 ≤ (20 / 3) * Real.log 2 := by
  have hl := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)
  norm_num at hl
  have he : Real.log (100 : ℝ) = 6 * Real.log 2 + 2 * Real.log (5 / 4) := by
    rw [show (100 : ℝ) = 2 ^ (6 : ℕ) * (5 / 4) ^ (2 : ℕ) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ^ (6 : ℕ) ≠ 0)
        (by norm_num : (5 / 4 : ℝ) ^ (2 : ℕ) ≠ 0), Real.log_pow, Real.log_pow]
    norm_num
  have hu := Real.log_le_log (by norm_num : (0 : ℝ) < 100 ^ (3 : ℕ))
    (show (100 : ℝ) ^ (3 : ℕ) ≤ 2 ^ (20 : ℕ) by norm_num)
  rw [Real.log_pow, Real.log_pow] at hu
  norm_num at hu
  constructor
  · rw [he]
    linarith only [hl]
  · linarith only [hu]

theorem anchor_entropy_bounds :
    (2 / 25 : ℝ) ≤ H (1 / 100) ∧ H (1 / 100) ≤ 11 / 100 ∧
    10 / 179 ≤ Real.log 2 * H (1 / 100) := by
  have hLlo : (693 / 1000 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hLhi : Real.log 2 ≤ (25 / 36 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hlog : Real.log ((1 / 100 : ℝ)⁻¹) ≤ (20 / 3) * Real.log 2 := by
    simpa using log_hundred_bounds.2
  have hu := (PsiOuterEntropy2048.entropy_logit_upper
    (p := (1 / 100 : ℝ)) (n := 20 / 3) (by norm_num) (by norm_num) hlog).1
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 99 / 100)
  have he : Real.log 2 * H (1 / 100) =
      (1 / 100) * Real.log 100 - (99 / 100) * Real.log (99 / 100) := by
    unfold H Real.binEntropy
    rw [mul_div_cancel₀ _ log_two_pos.ne']
    norm_num
    rw [show (100 / 99 : ℝ) = (99 / 100)⁻¹ by norm_num, Real.log_inv]
    ring
  have hn : (6 / 100) * Real.log 2 + 4 / 900 + 99 / 10000 ≤ Real.log 2 * H (1 / 100) := by
    rw [he]
    linarith only [hl, log_hundred_bounds.1]
  have hn' : (10 / 179 : ℝ) ≤ Real.log 2 * H (1 / 100) := by
    linarith only [hn, hLlo]
  refine ⟨?_, by linarith only [hu], hn'⟩
  apply (mul_le_mul_iff_left₀ log_two_pos).mp
  nlinarith only [hn', hLhi]

theorem anchor_compensated_slope :
    deriv eta (H (1 / 100)) + 1 / (Real.log 2 * H (1 / 100)) ≤ -(11 / 2) := by
  have hHpos : 0 < H (1 / 100) := H_pos (by norm_num) (by norm_num)
  have hHlt : H (1 / 100) < 1 := by linarith [anchor_entropy_bounds.2.1]
  have hL : Real.log 2 ≤ (25 / 36 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 99 ^ (30 : ℕ))
    (show (99 : ℝ) ^ (30 : ℕ) ≤ 2 ^ (199 : ℕ) by norm_num)
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  have hJ : J (1 / 100) ≤ (199 / 30 : ℝ) := by
    unfold J
    norm_num
    apply (div_le_iff₀ log_two_pos).mpr
    linarith only [hlog]
  have hJpos : 0 < J (1 / 100) := J_pos (by norm_num) (by norm_num)
  have hdpos : 0 < Real.log 2 * (1 / 100) * (1 - 1 / 100) * J (1 / 100) := by positivity
  have hprod := mul_le_mul hL hJ hJpos.le (by norm_num : (0 : ℝ) ≤ 25 / 36)
  have hquot : (107 / 5 : ℝ) ≤ (1 - 2 * (1 / 100)) /
      (Real.log 2 * (1 / 100) * (1 - 1 / 100) * J (1 / 100)) := by
    apply (le_div_iff₀ hdpos).mpr
    nlinarith only [hprod]
  have hinv : 1 / (Real.log 2 * H (1 / 100)) ≤ (179 / 10 : ℝ) := by
    apply (div_le_iff₀ (mul_pos log_two_pos hHpos)).mpr
    linarith only [anchor_entropy_bounds.2.2]
  rw [deriv_eta hHpos hHlt,
    entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num)]
  linarith only [hquot, hinv]

theorem neg_deriv_eta_ge_eleven_halves_logarithmic {h : ℝ}
    (hh : 0 < h) (hcap : h ≤ 2 / 25) :
    11 / 2 + 1 / (Real.log 2 * h) ≤ -deriv eta h := by
  have hc := (compensated_convexOn (r := 0) (by norm_num)).monotoneOn_deriv
    (fun x hx => (hasDerivAt_compensated (r := 0) (by norm_num) hx.1
      (by linarith [hx.2])).differentiableAt)
  have ha := anchor_entropy_bounds
  have hhH : h ≤ H (1 / 100) := hcap.trans ha.1
  have hp : 0 < H (1 / 100) := H_pos (by norm_num) (by norm_num)
  have hm := hc (show h ∈ Ioc 0 (11 / 100) from ⟨hh, by linarith⟩)
    (show H (1 / 100) ∈ Ioc 0 (11 / 100) from ⟨hp, ha.2.1⟩) hhH
  rw [(hasDerivAt_compensated (r := 0) (by norm_num) hh (by linarith)).deriv,
    (hasDerivAt_compensated (r := 0) (by norm_num) hp (by linarith [ha.2.1])).deriv,
    EntropyCurvature.radialPhi_zero] at hm
  simp only [compensation, mul_zero, zero_div, sub_zero, div_div] at hm
  linarith only [hm, anchor_compensated_slope]

theorem eta_add_eleven_halves_linear_log_antitone :
    AntitoneOn (fun h : ℝ => eta h + (11 / 2) * h + Real.log h / Real.log 2) (Ioc 0 (2 / 25)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 (2 / 25))
    (f' := fun h => deriv eta h + 11 / 2 + 1 / (Real.log 2 * h))
  · apply ContinuousOn.add
    · exact (Scalar.eta_continuousOn.mono (by intro h hh; exact ⟨hh.1, by linarith [hh.2]⟩)).add
        (continuous_const.mul continuous_id).continuousOn
    · exact (Real.continuousOn_log.mono (by intro h hh; exact ne_of_gt hh.1)).div_const _
  · intro h hh
    have hi : h ∈ Ioo (0 : ℝ) (2 / 25) := by simpa only [interior_Ioc] using hh
    have hd := ((hasDerivAt_eta hi.1 (by linarith [hi.2])).add
      ((hasDerivAt_id h).const_mul (11 / 2))).add ((Real.hasDerivAt_log hi.1.ne').div_const (Real.log 2))
    rw [← (hasDerivAt_eta hi.1 (by linarith [hi.2])).deriv] at hd
    convert! hd.hasDerivWithinAt using 1
    field_simp
  · intro h hh
    have hi : h ∈ Ioo (0 : ℝ) (2 / 25) := by simpa only [interior_Ioc] using hh
    linarith [neg_deriv_eta_ge_eleven_halves_logarithmic hi.1 hi.2.le]

theorem eta_increment_ge_eleven_halves_linear_log {a c : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hac : a + c ≤ 2 / 25) :
    (11 / 2) * c + Real.log (1 + c / a) / Real.log 2 ≤ eta a - eta (a + c) := by
  have hb : 0 < a + c := by linarith
  have hm := eta_add_eleven_halves_linear_log_antitone
    (show a ∈ Ioc (0 : ℝ) (2 / 25) from ⟨ha, by linarith⟩)
    (show a + c ∈ Ioc (0 : ℝ) (2 / 25) from ⟨hb, hac⟩) (by linarith)
  have he : 1 + c / a = (a + c) / a := by field_simp
  rw [he, Real.log_div hb.ne' ha.ne', sub_div]
  linarith

end GeneralCK.PsiParentElevenHalvesGain

#print axioms GeneralCK.PsiParentElevenHalvesGain.log_hundred_bounds
#print axioms GeneralCK.PsiParentElevenHalvesGain.anchor_entropy_bounds
#print axioms GeneralCK.PsiParentElevenHalvesGain.anchor_compensated_slope
#print axioms GeneralCK.PsiParentElevenHalvesGain.neg_deriv_eta_ge_eleven_halves_logarithmic
#print axioms GeneralCK.PsiParentElevenHalvesGain.eta_add_eleven_halves_linear_log_antitone
#print axioms GeneralCK.PsiParentElevenHalvesGain.eta_increment_ge_eleven_halves_linear_log

end


