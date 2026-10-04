-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g12
-- name    : CK_CKLaneC2R_CompactCover_S00_g12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T00:09:46.543757+00:00
-- url     : https://prove2.me/theorems/789e4745-0950-41f7-a44b-e5f4f7a4306b
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B035
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B037

namespace CKLaneC2R.CompactCover

theorem strip0_s015 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((49/320 : ℚ) : ℝ))) (h133 : z ≤ ((217/400 : ℚ) : ℝ)) (h134 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h135 : a ≤ ((99/640 : ℚ) : ℝ)) (h136 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h153 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h154 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h155 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B035.c713_pos (not_le.mp h3).le h135 (not_le.mp h136).le h155
      · -- right
        exact CKLaneC2R.Cells.S00.B035.c715_pos (not_le.mp h3).le h135 (not_le.mp h155).le h154
    · -- right
      by_cases h156 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B036.c721_pos (not_le.mp h3).le h135 (not_le.mp h154).le h156
      · -- right
        exact CKLaneC2R.Cells.S00.B036.c723_pos (not_le.mp h3).le h135 (not_le.mp h156).le h153
  · -- right
    by_cases h157 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h158 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B037.c745_pos (not_le.mp h3).le h135 (not_le.mp h153).le h158
      · -- right
        exact CKLaneC2R.Cells.S00.B037.c747_pos (not_le.mp h3).le h135 (not_le.mp h158).le h157
    · -- right
      by_cases h159 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B037.c753_pos (not_le.mp h3).le h135 (not_le.mp h157).le h159
      · -- right
        exact CKLaneC2R.Cells.S00.B037.c755_pos (not_le.mp h3).le h135 (not_le.mp h159).le h134

end CKLaneC2R.CompactCover


