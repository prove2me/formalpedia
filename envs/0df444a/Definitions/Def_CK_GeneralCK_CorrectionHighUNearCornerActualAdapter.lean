-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerActualAdapter
-- name    : CK_GeneralCK_CorrectionHighUNearCornerActualAdapter
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:00:29.44764+00:00
-- url     : https://prove2.me/theorems/39e33416-7a1b-468d-91e7-ee8b3177f495
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHighUNearCornerActualAdapter` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHighUNearCornerActualAdapter` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHighUNearCornerActualAdapter` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHighUNearCornerActualAdapter (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHighUNearCornerActualAdapter.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerWedgeAdapter

/-!
Pointwise bridge from the high-u raw corner wedges to the actual correction
Hessian minors. The raw numerical inequalities remain an explicit premise.
-/

namespace GeneralCK.Correction.HighU

theorem nearCorner_actual_ratio_of_raw_wedges
    (h : NearCornerRawWedgeTarget) {t rho : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    ActualRatioMinorsPositive (1 / 2 - t) rho := by
  let u : ℝ := 1 / 2 - t
  let w : ℝ := u + rho * (1 / 2 - u)
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hu1 : u < 1 / 2 := by dsimp [u]; linarith
  have hrOne : rho < 1 := by linarith
  obtain ⟨huw, hw⟩ := Natural.ratio_point_interior (sub_pos.mpr hu1) hr hrOne
  have huw' : u < w := by simpa only [w] using huw
  have hw' : w < 1 / 2 := by simpa only [w] using hw
  have hw0 : 0 < H w := H_pos (hu0.trans huw') (by linarith [hw'])
  have hw1 : H w < 1 := by
    have hs := H_strictMonoOn
      ⟨(hu0.trans huw').le, hw'.le⟩
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2)) hw'
    simpa only [H_half] using hs
  have hcoord : 1 / 2 - (1 - rho) * t = w := by
    dsimp [w, u]; ring
  obtain ⟨hm, hk⟩ := nearCorner_scaled_margins_of_raw_wedges h ht ht1 hr hr1
  have hmPosRatio :
      0 < Natural.m11 u w / t ^ 2 := by
    rw [← hcoord]
    dsimp [u]
    exact (show (0 : ℝ) < 1 / 2 by norm_num).trans_le hm
  have hkPosRatio :
      0 < Natural.kdet u w /
        (rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2)) := by
    rw [← hcoord]
    dsimp [u]
    exact (show (0 : ℝ) < 1 by norm_num).trans_le hk
  have ht2 : 0 < t ^ 2 := by positivity
  have hden : 0 < rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2) := by positivity
  have hmPos : 0 < Natural.m11 u w := by
    have hp := mul_pos hmPosRatio ht2
    rwa [div_mul_cancel₀ _ ht2.ne'] at hp
  have hkPos : 0 < Natural.kdet u w := by
    have hp := mul_pos hkPosRatio hden
    rwa [div_mul_cancel₀ _ hden.ne'] at hp
  have heq := Natural.kernel_eq_actual_ratio hu0 (sub_pos.mpr hu1) hr hrOne
  change ActualRatioMinorsPositive u rho
  unfold ActualRatioMinorsPositive
  dsimp [w] at hmPos hkPos ⊢
  refine ⟨heq.1 ▸ hmPos, ?_⟩
  exact (Mdet_pos_iff_Kfactored_pos hw0 hw1).2 (heq.2 ▸ hkPos)

#print axioms nearCorner_actual_ratio_of_raw_wedges

end GeneralCK.Correction.HighU


