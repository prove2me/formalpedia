-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g105_q00
-- name    : CK_CKLaneC2R_CompactCover_S00_g105_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T19:33:45.062417+00:00
-- url     : https://prove2.me/theorems/618cfceb-a6de-493e-b4ab-ce717a840f8d
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00 (proof part of strip0) (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00 (proof part of strip0) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00 (proof part of strip0) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (proof part of strip0) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00 (proof part of strip0) (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B015
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B001


namespace CKLaneC2R.CompactCover

theorem strip0_s132 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : ¬ (a ≤ ((31/160 : ℚ) : ℝ))) (h1381 : z ≤ ((217/400 : ℚ) : ℝ)) (h1382 : ¬ (a ≤ ((63/320 : ℚ) : ℝ))) (h1417 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1418 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1434 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h1435 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1436 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B012.c243_pos (not_le.mp h1382).le ha2 (not_le.mp h1418).le h1436
      · -- right
        exact CKLaneC2R.Cells.S00.B012.c244_pos (not_le.mp h1382).le ha2 (not_le.mp h1436).le h1435
    · -- right
      by_cases h1437 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B012.c247_pos (not_le.mp h1382).le ha2 (not_le.mp h1435).le h1437
      · -- right
        exact CKLaneC2R.Cells.S00.B012.c248_pos (not_le.mp h1382).le ha2 (not_le.mp h1437).le h1434
  · -- right
    by_cases h1438 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1439 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B012.c259_pos (not_le.mp h1382).le ha2 (not_le.mp h1434).le h1439
      · -- right
        exact CKLaneC2R.Cells.S00.B013.c260_pos (not_le.mp h1382).le ha2 (not_le.mp h1439).le h1438
    · -- right
      by_cases h1440 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B013.c263_pos (not_le.mp h1382).le ha2 (not_le.mp h1438).le h1440
      · -- right
        exact CKLaneC2R.Cells.S00.B013.c264_pos (not_le.mp h1382).le ha2 (not_le.mp h1440).le h1417

end CKLaneC2R.CompactCover


