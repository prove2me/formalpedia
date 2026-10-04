-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g13
-- name    : CK_CKLaneC2R_CompactCover_S00_g13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T04:32:54.708164+00:00
-- url     : https://prove2.me/theorems/d31fb5ad-49e4-4faa-94ac-4c0ecee3f17c
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

namespace CKLaneC2R.CompactCover

theorem strip0_s016 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((49/320 : ℚ) : ℝ))) (h133 : z ≤ ((217/400 : ℚ) : ℝ)) (h134 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h135 : ¬ (a ≤ ((99/640 : ℚ) : ℝ))) (h160 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h161 : z ≤ ((2289/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h162 : z ≤ ((733/6400 : ℚ) : ℝ)
  · -- left
    by_cases h163 : z ≤ ((6417/64000 : ℚ) : ℝ)
    · -- left
      by_cases h164 : z ≤ ((11921/128000 : ℚ) : ℝ)
      · -- left
        by_cases h165 : z ≤ ((22929/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B069.c1380_pos (not_le.mp h135).le h2 hz1 h165
        · -- right
          exact CKLaneC2R.Cells.S00.B069.c1381_pos (not_le.mp h135).le h2 (not_le.mp h165).le h164
      · -- right
        by_cases h166 : z ≤ ((4951/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B069.c1384_pos (not_le.mp h135).le h2 (not_le.mp h164).le h166
        · -- right
          exact CKLaneC2R.Cells.S00.B069.c1385_pos (not_le.mp h135).le h2 (not_le.mp h166).le h163
    · -- right
      by_cases h167 : z ≤ ((13747/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B053.c1063_pos (not_le.mp h135).le h2 (not_le.mp h163).le h167
      · -- right
        exact CKLaneC2R.Cells.S00.B053.c1065_pos (not_le.mp h135).le h2 (not_le.mp h167).le h162
  · -- right
    by_cases h168 : z ≤ ((8243/64000 : ℚ) : ℝ)
    · -- left
      by_cases h169 : z ≤ ((15573/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B054.c1081_pos (not_le.mp h135).le h2 (not_le.mp h162).le h169
      · -- right
        exact CKLaneC2R.Cells.S00.B054.c1083_pos (not_le.mp h135).le h2 (not_le.mp h169).le h168
    · -- right
      by_cases h170 : z ≤ ((17399/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B054.c1089_pos (not_le.mp h135).le h2 (not_le.mp h168).le h170
      · -- right
        exact CKLaneC2R.Cells.S00.B054.c1091_pos (not_le.mp h135).le h2 (not_le.mp h170).le h161

end CKLaneC2R.CompactCover


