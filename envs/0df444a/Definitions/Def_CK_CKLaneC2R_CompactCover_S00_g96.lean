-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g96
-- name    : CK_CKLaneC2R_CompactCover_S00_g96
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T19:58:59.817844+00:00
-- url     : https://prove2.me/theorems/58ecb1e6-3281-474a-9a59-e1129c2525a7
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B015
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B000

namespace CKLaneC2R.CompactCover

theorem strip0_s121 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : z ≤ ((217/400 : ℚ) : ℝ)) (h1240 : ¬ (a ≤ ((61/320 : ℚ) : ℝ))) (h1278 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1304 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h1305 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1306 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1307 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B014.c299_pos (not_le.mp h1240).le h1238 (not_le.mp h1278).le h1307
        · -- right
          exact CKLaneC2R.Cells.S00.B015.c300_pos (not_le.mp h1240).le h1238 (not_le.mp h1307).le h1306
      · -- right
        by_cases h1308 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B015.c303_pos (not_le.mp h1240).le h1238 (not_le.mp h1306).le h1308
        · -- right
          exact CKLaneC2R.Cells.S00.B015.c304_pos (not_le.mp h1240).le h1238 (not_le.mp h1308).le h1305
    · -- right
      by_cases h1309 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h1310 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B015.c315_pos (not_le.mp h1240).le h1238 (not_le.mp h1305).le h1310
        · -- right
          exact CKLaneC2R.Cells.S00.B015.c316_pos (not_le.mp h1240).le h1238 (not_le.mp h1310).le h1309
      · -- right
        exact CKLaneC2R.Cells.S00.B000.c0_pos (not_le.mp h1240).le h1238 (not_le.mp h1309).le h1304
  · -- right
    by_cases h1311 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1312 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B000.c9_pos (not_le.mp h1240).le h1238 (not_le.mp h1304).le h1312
      · -- right
        exact CKLaneC2R.Cells.S00.B000.c11_pos (not_le.mp h1240).le h1238 (not_le.mp h1312).le h1311
    · -- right
      by_cases h1313 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B000.c17_pos (not_le.mp h1240).le h1238 (not_le.mp h1311).le h1313
      · -- right
        exact CKLaneC2R.Cells.S00.B000.c19_pos (not_le.mp h1240).le h1238 (not_le.mp h1313).le h1239

end CKLaneC2R.CompactCover


