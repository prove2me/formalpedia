-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g12
-- name    : CK_CKLaneC2R_CompactCover_S01_g12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T04:28:18.156974+00:00
-- url     : https://prove2.me/theorems/dc5151d4-56ad-4667-9d54-b2292606e157
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B047
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B048
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B032

namespace CKLaneC2R.CompactCover

theorem strip1_s014 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((33/160 : ℚ) : ℝ))) (h118 : z ≤ ((217/400 : ℚ) : ℝ)) (h119 : ¬ (a ≤ ((67/320 : ℚ) : ℝ))) (h148 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h149 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h150 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h151 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h152 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h153 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B047.c958_pos (not_le.mp h119).le h2 hz1 h153
        · -- right
          exact CKLaneC2R.Cells.S01.B047.c959_pos (not_le.mp h119).le h2 (not_le.mp h153).le h152
      · -- right
        by_cases h154 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B048.c962_pos (not_le.mp h119).le h2 (not_le.mp h152).le h154
        · -- right
          exact CKLaneC2R.Cells.S01.B048.c963_pos (not_le.mp h119).le h2 (not_le.mp h154).le h151
    · -- right
      by_cases h155 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h156 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B048.c974_pos (not_le.mp h119).le h2 (not_le.mp h151).le h156
        · -- right
          exact CKLaneC2R.Cells.S01.B048.c975_pos (not_le.mp h119).le h2 (not_le.mp h156).le h155
      · -- right
        by_cases h157 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B048.c978_pos (not_le.mp h119).le h2 (not_le.mp h155).le h157
        · -- right
          exact CKLaneC2R.Cells.S01.B048.c979_pos (not_le.mp h119).le h2 (not_le.mp h157).le h150
  · -- right
    by_cases h158 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h159 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B031.c636_pos (not_le.mp h119).le h2 (not_le.mp h150).le h159
      · -- right
        exact CKLaneC2R.Cells.S01.B031.c638_pos (not_le.mp h119).le h2 (not_le.mp h159).le h158
    · -- right
      by_cases h160 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B032.c644_pos (not_le.mp h119).le h2 (not_le.mp h158).le h160
      · -- right
        exact CKLaneC2R.Cells.S01.B032.c646_pos (not_le.mp h119).le h2 (not_le.mp h160).le h149

end CKLaneC2R.CompactCover


