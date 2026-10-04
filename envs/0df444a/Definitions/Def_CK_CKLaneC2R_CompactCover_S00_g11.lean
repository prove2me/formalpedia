-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g11
-- name    : CK_CKLaneC2R_CompactCover_S00_g11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T09:06:28.041842+00:00
-- url     : https://prove2.me/theorems/a7ef777a-f8da-4d08-8aa0-6387b7c67ce5
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B056
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B033

namespace CKLaneC2R.CompactCover

theorem strip0_s014 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((49/320 : ℚ) : ℝ))) (h133 : z ≤ ((217/400 : ℚ) : ℝ)) (h134 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h135 : a ≤ ((99/640 : ℚ) : ℝ)) (h136 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h137 : ¬ (z ≤ ((2289/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h147 : z ≤ ((5491/32000 : ℚ) : ℝ)
  · -- left
    by_cases h148 : z ≤ ((10069/64000 : ℚ) : ℝ)
    · -- left
      by_cases h149 : z ≤ ((769/5120 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B055.c1116_pos (not_le.mp h3).le h135 (not_le.mp h137).le h149
      · -- right
        exact CKLaneC2R.Cells.S00.B055.c1118_pos (not_le.mp h3).le h135 (not_le.mp h149).le h148
    · -- right
      by_cases h150 : z ≤ ((21051/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B056.c1120_pos (not_le.mp h3).le h135 (not_le.mp h148).le h150
      · -- right
        exact CKLaneC2R.Cells.S00.B056.c1121_pos (not_le.mp h3).le h135 (not_le.mp h150).le h147
  · -- right
    by_cases h151 : z ≤ ((2379/12800 : ℚ) : ℝ)
    · -- left
      by_cases h152 : z ≤ ((22877/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B056.c1128_pos (not_le.mp h3).le h135 (not_le.mp h147).le h152
      · -- right
        exact CKLaneC2R.Cells.S00.B056.c1129_pos (not_le.mp h3).le h135 (not_le.mp h152).le h151
    · -- right
      exact CKLaneC2R.Cells.S00.B033.c674_pos (not_le.mp h3).le h135 (not_le.mp h151).le h136

end CKLaneC2R.CompactCover


