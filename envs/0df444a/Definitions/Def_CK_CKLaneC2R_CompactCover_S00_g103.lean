-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g103
-- name    : CK_CKLaneC2R_CompactCover_S00_g103
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T14:35:03.157379+00:00
-- url     : https://prove2.me/theorems/97f702f7-e15f-4312-ac09-f460005f88d4
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B015
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B001

namespace CKLaneC2R.CompactCover

theorem strip0_s130 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : ¬ (a ≤ ((31/160 : ℚ) : ℝ))) (h1381 : z ≤ ((217/400 : ℚ) : ℝ)) (h1382 : a ≤ ((63/320 : ℚ) : ℝ)) (h1383 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1407 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h1408 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1409 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1410 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B015.c305_pos (not_le.mp h1238).le h1382 (not_le.mp h1383).le h1410
        · -- right
          exact CKLaneC2R.Cells.S00.B015.c306_pos (not_le.mp h1238).le h1382 (not_le.mp h1410).le h1409
      · -- right
        by_cases h1411 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B015.c309_pos (not_le.mp h1238).le h1382 (not_le.mp h1409).le h1411
        · -- right
          exact CKLaneC2R.Cells.S00.B015.c310_pos (not_le.mp h1238).le h1382 (not_le.mp h1411).le h1408
    · -- right
      by_cases h1412 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h1413 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B015.c319_pos (not_le.mp h1238).le h1382 (not_le.mp h1408).le h1413
        · -- right
          exact CKLaneC2R.Cells.S00.B016.c320_pos (not_le.mp h1238).le h1382 (not_le.mp h1413).le h1412
      · -- right
        exact CKLaneC2R.Cells.S00.B000.c2_pos (not_le.mp h1238).le h1382 (not_le.mp h1412).le h1407
  · -- right
    by_cases h1414 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1415 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B000.c12_pos (not_le.mp h1238).le h1382 (not_le.mp h1407).le h1415
      · -- right
        exact CKLaneC2R.Cells.S00.B000.c14_pos (not_le.mp h1238).le h1382 (not_le.mp h1415).le h1414
    · -- right
      by_cases h1416 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B001.c20_pos (not_le.mp h1238).le h1382 (not_le.mp h1414).le h1416
      · -- right
        exact CKLaneC2R.Cells.S00.B001.c22_pos (not_le.mp h1238).le h1382 (not_le.mp h1416).le h1381

end CKLaneC2R.CompactCover


