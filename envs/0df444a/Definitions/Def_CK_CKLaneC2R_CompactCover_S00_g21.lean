-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g21
-- name    : CK_CKLaneC2R_CompactCover_S00_g21
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T10:33:08.221991+00:00
-- url     : https://prove2.me/theorems/6501916c-7ba7-4427-93ad-649ecfafc598
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B069
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B053
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B054
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B056
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B033

namespace CKLaneC2R.CompactCover

theorem strip0_s026 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : a ≤ ((51/320 : ℚ) : ℝ)) (h254 : z ≤ ((217/400 : ℚ) : ℝ)) (h255 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h256 : a ≤ ((101/640 : ℚ) : ℝ)) (h257 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h258 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h259 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h260 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h261 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          by_cases h262 : z ≤ ((22929/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B069.c1390_pos (not_le.mp h2).le h256 hz1 h262
          · -- right
            exact CKLaneC2R.Cells.S00.B069.c1391_pos (not_le.mp h2).le h256 (not_le.mp h262).le h261
        · -- right
          by_cases h263 : z ≤ ((4951/51200 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B069.c1394_pos (not_le.mp h2).le h256 (not_le.mp h261).le h263
          · -- right
            exact CKLaneC2R.Cells.S00.B069.c1395_pos (not_le.mp h2).le h256 (not_le.mp h263).le h260
      · -- right
        by_cases h264 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B053.c1068_pos (not_le.mp h2).le h256 (not_le.mp h260).le h264
        · -- right
          exact CKLaneC2R.Cells.S00.B053.c1070_pos (not_le.mp h2).le h256 (not_le.mp h264).le h259
    · -- right
      by_cases h265 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h266 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B054.c1092_pos (not_le.mp h2).le h256 (not_le.mp h259).le h266
        · -- right
          exact CKLaneC2R.Cells.S00.B054.c1094_pos (not_le.mp h2).le h256 (not_le.mp h266).le h265
      · -- right
        by_cases h267 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B055.c1100_pos (not_le.mp h2).le h256 (not_le.mp h265).le h267
        · -- right
          exact CKLaneC2R.Cells.S00.B055.c1102_pos (not_le.mp h2).le h256 (not_le.mp h267).le h258
  · -- right
    by_cases h268 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h269 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        by_cases h270 : z ≤ ((769/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B056.c1132_pos (not_le.mp h2).le h256 (not_le.mp h258).le h270
        · -- right
          exact CKLaneC2R.Cells.S00.B056.c1134_pos (not_le.mp h2).le h256 (not_le.mp h270).le h269
      · -- right
        by_cases h271 : z ≤ ((21051/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B056.c1136_pos (not_le.mp h2).le h256 (not_le.mp h269).le h271
        · -- right
          exact CKLaneC2R.Cells.S00.B056.c1137_pos (not_le.mp h2).le h256 (not_le.mp h271).le h268
    · -- right
      by_cases h272 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B033.c676_pos (not_le.mp h2).le h256 (not_le.mp h268).le h272
      · -- right
        exact CKLaneC2R.Cells.S00.B033.c678_pos (not_le.mp h2).le h256 (not_le.mp h272).le h257

end CKLaneC2R.CompactCover


