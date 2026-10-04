-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g91
-- name    : CK_CKLaneC2R_CompactCover_S00_g91
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T10:19:06.7713+00:00
-- url     : https://prove2.me/theorems/7169f550-bfec-4128-9c1a-030fb7f2b8bd
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B063
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B042

namespace CKLaneC2R.CompactCover

theorem strip0_s114 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : z ≤ ((217/400 : ℚ) : ℝ)) (h1240 : a ≤ ((61/320 : ℚ) : ℝ)) (h1241 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1242 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h1243 : z ≤ ((2289/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1244 : z ≤ ((733/6400 : ℚ) : ℝ)
  · -- left
    by_cases h1245 : z ≤ ((6417/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1246 : a ≤ ((121/640 : ℚ) : ℝ)
      · -- left
        by_cases h1247 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B063.c1269_pos (not_le.mp h891).le h1246 hz1 h1247
        · -- right
          exact CKLaneC2R.Cells.S00.B063.c1271_pos (not_le.mp h891).le h1246 (not_le.mp h1247).le h1245
      · -- right
        by_cases h1248 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B063.c1270_pos (not_le.mp h1246).le h1240 hz1 h1248
        · -- right
          exact CKLaneC2R.Cells.S00.B063.c1272_pos (not_le.mp h1246).le h1240 (not_le.mp h1248).le h1245
    · -- right
      by_cases h1249 : z ≤ ((13747/128000 : ℚ) : ℝ)
      · -- left
        by_cases h1250 : a ≤ ((121/640 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B063.c1277_pos (not_le.mp h891).le h1250 (not_le.mp h1245).le h1249
        · -- right
          exact CKLaneC2R.Cells.S00.B063.c1278_pos (not_le.mp h1250).le h1240 (not_le.mp h1245).le h1249
      · -- right
        exact CKLaneC2R.Cells.S00.B041.c839_pos (not_le.mp h891).le h1240 (not_le.mp h1249).le h1244
  · -- right
    by_cases h1251 : z ≤ ((8243/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1252 : z ≤ ((15573/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B042.c845_pos (not_le.mp h891).le h1240 (not_le.mp h1244).le h1252
      · -- right
        exact CKLaneC2R.Cells.S00.B042.c846_pos (not_le.mp h891).le h1240 (not_le.mp h1252).le h1251
    · -- right
      by_cases h1253 : z ≤ ((17399/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B042.c849_pos (not_le.mp h891).le h1240 (not_le.mp h1251).le h1253
      · -- right
        exact CKLaneC2R.Cells.S00.B042.c850_pos (not_le.mp h891).le h1240 (not_le.mp h1253).le h1243

end CKLaneC2R.CompactCover


