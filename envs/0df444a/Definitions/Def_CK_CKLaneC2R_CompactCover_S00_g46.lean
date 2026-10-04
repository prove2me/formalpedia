-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g46
-- name    : CK_CKLaneC2R_CompactCover_S00_g46
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T09:12:13.981742+00:00
-- url     : https://prove2.me/theorems/18693ca8-7d09-4f40-ba06-0b462280ff9b
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B057
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B059
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B060
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B034

namespace CKLaneC2R.CompactCover

theorem strip0_s055 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : ¬ (a ≤ ((53/320 : ℚ) : ℝ))) (h590 : z ≤ ((217/400 : ℚ) : ℝ)) (h591 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h592 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h593 : z ≤ ((2289/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h594 : a ≤ ((107/640 : ℚ) : ℝ)
  · -- left
    by_cases h595 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h596 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h597 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B057.c1151_pos (not_le.mp h482).le h594 hz1 h597
        · -- right
          exact CKLaneC2R.Cells.S00.B057.c1153_pos (not_le.mp h482).le h594 (not_le.mp h597).le h596
      · -- right
        by_cases h598 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B057.c1159_pos (not_le.mp h482).le h594 (not_le.mp h596).le h598
        · -- right
          exact CKLaneC2R.Cells.S00.B058.c1161_pos (not_le.mp h482).le h594 (not_le.mp h598).le h595
    · -- right
      by_cases h599 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h600 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B059.c1183_pos (not_le.mp h482).le h594 (not_le.mp h595).le h600
        · -- right
          exact CKLaneC2R.Cells.S00.B059.c1185_pos (not_le.mp h482).le h594 (not_le.mp h600).le h599
      · -- right
        by_cases h601 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B059.c1191_pos (not_le.mp h482).le h594 (not_le.mp h599).le h601
        · -- right
          exact CKLaneC2R.Cells.S00.B059.c1193_pos (not_le.mp h482).le h594 (not_le.mp h601).le h593
  · -- right
    by_cases h602 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h603 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h604 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B057.c1152_pos (not_le.mp h594).le h481 hz1 h604
        · -- right
          exact CKLaneC2R.Cells.S00.B057.c1154_pos (not_le.mp h594).le h481 (not_le.mp h604).le h603
      · -- right
        by_cases h605 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B058.c1160_pos (not_le.mp h594).le h481 (not_le.mp h603).le h605
        · -- right
          exact CKLaneC2R.Cells.S00.B058.c1162_pos (not_le.mp h594).le h481 (not_le.mp h605).le h602
    · -- right
      by_cases h606 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h607 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B059.c1184_pos (not_le.mp h594).le h481 (not_le.mp h602).le h607
        · -- right
          exact CKLaneC2R.Cells.S00.B059.c1186_pos (not_le.mp h594).le h481 (not_le.mp h607).le h606
      · -- right
        by_cases h608 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B059.c1192_pos (not_le.mp h594).le h481 (not_le.mp h606).le h608
        · -- right
          exact CKLaneC2R.Cells.S00.B059.c1194_pos (not_le.mp h594).le h481 (not_le.mp h608).le h593

theorem strip0_s056 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : ¬ (a ≤ ((53/320 : ℚ) : ℝ))) (h590 : z ≤ ((217/400 : ℚ) : ℝ)) (h591 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h592 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h593 : ¬ (z ≤ ((2289/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h609 : z ≤ ((5491/32000 : ℚ) : ℝ)
  · -- left
    by_cases h610 : z ≤ ((10069/64000 : ℚ) : ℝ)
    · -- left
      by_cases h611 : a ≤ ((107/640 : ℚ) : ℝ)
      · -- left
        by_cases h612 : z ≤ ((769/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B060.c1215_pos (not_le.mp h482).le h611 (not_le.mp h593).le h612
        · -- right
          exact CKLaneC2R.Cells.S00.B060.c1217_pos (not_le.mp h482).le h611 (not_le.mp h612).le h610
      · -- right
        by_cases h613 : z ≤ ((769/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B060.c1216_pos (not_le.mp h611).le h481 (not_le.mp h593).le h613
        · -- right
          exact CKLaneC2R.Cells.S00.B060.c1218_pos (not_le.mp h611).le h481 (not_le.mp h613).le h610
    · -- right
      by_cases h614 : z ≤ ((21051/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B034.c684_pos (not_le.mp h482).le h481 (not_le.mp h610).le h614
      · -- right
        exact CKLaneC2R.Cells.S00.B034.c685_pos (not_le.mp h482).le h481 (not_le.mp h614).le h609
  · -- right
    by_cases h615 : a ≤ ((107/640 : ℚ) : ℝ)
    · -- left
      by_cases h616 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B034.c690_pos (not_le.mp h482).le h615 (not_le.mp h609).le h616
      · -- right
        exact CKLaneC2R.Cells.S00.B034.c692_pos (not_le.mp h482).le h615 (not_le.mp h616).le h592
    · -- right
      by_cases h617 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B034.c691_pos (not_le.mp h615).le h481 (not_le.mp h609).le h617
      · -- right
        exact CKLaneC2R.Cells.S00.B034.c693_pos (not_le.mp h615).le h481 (not_le.mp h617).le h592

end CKLaneC2R.CompactCover


