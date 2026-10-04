-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g94
-- name    : CK_CKLaneC2R_CompactCover_S00_g94
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T14:08:29.852093+00:00
-- url     : https://prove2.me/theorems/32c076df-012f-4e2a-a4d9-4150c0b69613
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
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B064
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B042

namespace CKLaneC2R.CompactCover

theorem strip0_s118 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : z ≤ ((217/400 : ℚ) : ℝ)) (h1240 : ¬ (a ≤ ((61/320 : ℚ) : ℝ))) (h1278 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1279 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h1280 : z ≤ ((2289/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1281 : z ≤ ((733/6400 : ℚ) : ℝ)
  · -- left
    by_cases h1282 : z ≤ ((6417/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1283 : a ≤ ((123/640 : ℚ) : ℝ)
      · -- left
        by_cases h1284 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B063.c1273_pos (not_le.mp h1240).le h1283 hz1 h1284
        · -- right
          exact CKLaneC2R.Cells.S00.B063.c1275_pos (not_le.mp h1240).le h1283 (not_le.mp h1284).le h1282
      · -- right
        by_cases h1285 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B063.c1274_pos (not_le.mp h1283).le h1238 hz1 h1285
        · -- right
          exact CKLaneC2R.Cells.S00.B063.c1276_pos (not_le.mp h1283).le h1238 (not_le.mp h1285).le h1282
    · -- right
      by_cases h1286 : z ≤ ((13747/128000 : ℚ) : ℝ)
      · -- left
        by_cases h1287 : a ≤ ((123/640 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B063.c1279_pos (not_le.mp h1240).le h1287 (not_le.mp h1282).le h1286
        · -- right
          exact CKLaneC2R.Cells.S00.B064.c1280_pos (not_le.mp h1287).le h1238 (not_le.mp h1282).le h1286
      · -- right
        exact CKLaneC2R.Cells.S00.B042.c840_pos (not_le.mp h1240).le h1238 (not_le.mp h1286).le h1281
  · -- right
    by_cases h1288 : z ≤ ((8243/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1289 : z ≤ ((15573/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B042.c847_pos (not_le.mp h1240).le h1238 (not_le.mp h1281).le h1289
      · -- right
        exact CKLaneC2R.Cells.S00.B042.c848_pos (not_le.mp h1240).le h1238 (not_le.mp h1289).le h1288
    · -- right
      by_cases h1290 : z ≤ ((17399/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B042.c851_pos (not_le.mp h1240).le h1238 (not_le.mp h1288).le h1290
      · -- right
        exact CKLaneC2R.Cells.S00.B042.c852_pos (not_le.mp h1240).le h1238 (not_le.mp h1290).le h1280

end CKLaneC2R.CompactCover


