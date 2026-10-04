-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g40
-- name    : CK_CKLaneC2R_CompactCover_S00_g40
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T06:53:31.903754+00:00
-- url     : https://prove2.me/theorems/598c63b8-058a-4bec-b648-3d68bdf04af1
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
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B059
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B060
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B061
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B034

namespace CKLaneC2R.CompactCover

theorem strip0_s047 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : a ≤ ((53/320 : ℚ) : ℝ)) (h483 : z ≤ ((217/400 : ℚ) : ℝ)) (h484 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h485 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h486 : ¬ (a ≤ ((21/128 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h501 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h502 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h503 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h504 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B057.c1148_pos (not_le.mp h486).le h482 hz1 h504
        · -- right
          exact CKLaneC2R.Cells.S00.B057.c1150_pos (not_le.mp h486).le h482 (not_le.mp h504).le h503
      · -- right
        by_cases h505 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B057.c1156_pos (not_le.mp h486).le h482 (not_le.mp h503).le h505
        · -- right
          exact CKLaneC2R.Cells.S00.B057.c1158_pos (not_le.mp h486).le h482 (not_le.mp h505).le h502
    · -- right
      by_cases h506 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h507 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B059.c1180_pos (not_le.mp h486).le h482 (not_le.mp h502).le h507
        · -- right
          exact CKLaneC2R.Cells.S00.B059.c1182_pos (not_le.mp h486).le h482 (not_le.mp h507).le h506
      · -- right
        by_cases h508 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B059.c1188_pos (not_le.mp h486).le h482 (not_le.mp h506).le h508
        · -- right
          exact CKLaneC2R.Cells.S00.B059.c1190_pos (not_le.mp h486).le h482 (not_le.mp h508).le h501
  · -- right
    by_cases h509 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h510 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        by_cases h511 : z ≤ ((769/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B060.c1212_pos (not_le.mp h486).le h482 (not_le.mp h501).le h511
        · -- right
          exact CKLaneC2R.Cells.S00.B060.c1214_pos (not_le.mp h486).le h482 (not_le.mp h511).le h510
      · -- right
        by_cases h512 : z ≤ ((21051/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B061.c1220_pos (not_le.mp h486).le h482 (not_le.mp h510).le h512
        · -- right
          exact CKLaneC2R.Cells.S00.B061.c1222_pos (not_le.mp h486).le h482 (not_le.mp h512).le h509
    · -- right
      by_cases h513 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B034.c687_pos (not_le.mp h486).le h482 (not_le.mp h509).le h513
      · -- right
        exact CKLaneC2R.Cells.S00.B034.c689_pos (not_le.mp h486).le h482 (not_le.mp h513).le h485

end CKLaneC2R.CompactCover


