-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g48
-- name    : CK_CKLaneC2R_CompactCover_S00_g48
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T15:06:43.590528+00:00
-- url     : https://prove2.me/theorems/d1d7e5b1-90ab-4d0b-80a2-556a6613d9c8
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (proof part of strip0) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00 (proof part of strip0).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B009

namespace CKLaneC2R.CompactCover

theorem strip0_s058 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : ¬ (a ≤ ((53/320 : ℚ) : ℝ))) (h590 : z ≤ ((217/400 : ℚ) : ℝ)) (h591 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h630 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h631 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h632 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h633 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B006.c137_pos (not_le.mp h482).le h481 (not_le.mp h591).le h633
        · -- right
          exact CKLaneC2R.Cells.S00.B006.c138_pos (not_le.mp h482).le h481 (not_le.mp h633).le h632
      · -- right
        by_cases h634 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B007.c141_pos (not_le.mp h482).le h481 (not_le.mp h632).le h634
        · -- right
          exact CKLaneC2R.Cells.S00.B007.c142_pos (not_le.mp h482).le h481 (not_le.mp h634).le h631
    · -- right
      by_cases h635 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h636 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B007.c153_pos (not_le.mp h482).le h481 (not_le.mp h631).le h636
        · -- right
          exact CKLaneC2R.Cells.S00.B007.c154_pos (not_le.mp h482).le h481 (not_le.mp h636).le h635
      · -- right
        by_cases h637 : z ≤ ((26503/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B007.c157_pos (not_le.mp h482).le h481 (not_le.mp h635).le h637
        · -- right
          exact CKLaneC2R.Cells.S00.B007.c158_pos (not_le.mp h482).le h481 (not_le.mp h637).le h630
  · -- right
    by_cases h638 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h639 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        by_cases h640 : z ≤ ((28329/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B008.c169_pos (not_le.mp h482).le h481 (not_le.mp h630).le h640
        · -- right
          exact CKLaneC2R.Cells.S00.B008.c170_pos (not_le.mp h482).le h481 (not_le.mp h640).le h639
      · -- right
        by_cases h641 : z ≤ ((6031/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B008.c173_pos (not_le.mp h482).le h481 (not_le.mp h639).le h641
        · -- right
          exact CKLaneC2R.Cells.S00.B008.c174_pos (not_le.mp h482).le h481 (not_le.mp h641).le h638
    · -- right
      by_cases h642 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        by_cases h643 : z ≤ ((31981/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B009.c185_pos (not_le.mp h482).le h481 (not_le.mp h638).le h643
        · -- right
          exact CKLaneC2R.Cells.S00.B009.c186_pos (not_le.mp h482).le h481 (not_le.mp h643).le h642
      · -- right
        by_cases h644 : z ≤ ((33807/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B009.c189_pos (not_le.mp h482).le h481 (not_le.mp h642).le h644
        · -- right
          exact CKLaneC2R.Cells.S00.B009.c190_pos (not_le.mp h482).le h481 (not_le.mp h644).le h590

end CKLaneC2R.CompactCover


