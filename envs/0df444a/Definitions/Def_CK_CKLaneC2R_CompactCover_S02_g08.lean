-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g08
-- name    : CK_CKLaneC2R_CompactCover_S02_g08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T20:57:07.317719+00:00
-- url     : https://prove2.me/theorems/b3a081b5-a129-4a1a-bd04-b9e7780fb514
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S02 (proof part of strip2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S02 (proof part of strip2).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B038
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B015

namespace CKLaneC2R.CompactCover

theorem strip2_s010 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((5/16 : ℚ) : ℝ))) (h93 : z ≤ ((217/400 : ℚ) : ℝ)) (h94 : ¬ (a ≤ ((51/160 : ℚ) : ℝ))) (h117 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h118 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h119 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h120 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h121 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          by_cases h122 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B038.c765_pos (not_le.mp h94).le h2 hz1 h122
          · -- right
            exact CKLaneC2R.Cells.S02.B038.c766_pos (not_le.mp h94).le h2 (not_le.mp h122).le h121
        · -- right
          by_cases h123 : z ≤ ((13747/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B038.c769_pos (not_le.mp h94).le h2 (not_le.mp h121).le h123
          · -- right
            exact CKLaneC2R.Cells.S02.B038.c770_pos (not_le.mp h94).le h2 (not_le.mp h123).le h120
      · -- right
        by_cases h124 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B029.c584_pos (not_le.mp h94).le h2 (not_le.mp h120).le h124
        · -- right
          exact CKLaneC2R.Cells.S02.B029.c586_pos (not_le.mp h94).le h2 (not_le.mp h124).le h119
    · -- right
      by_cases h125 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h126 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B029.c597_pos (not_le.mp h94).le h2 (not_le.mp h119).le h126
        · -- right
          exact CKLaneC2R.Cells.S02.B029.c598_pos (not_le.mp h94).le h2 (not_le.mp h126).le h125
      · -- right
        by_cases h127 : z ≤ ((2379/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B030.c601_pos (not_le.mp h94).le h2 (not_le.mp h125).le h127
        · -- right
          exact CKLaneC2R.Cells.S02.B030.c602_pos (not_le.mp h94).le h2 (not_le.mp h127).le h118
  · -- right
    by_cases h128 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h129 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B014.c293_pos (not_le.mp h94).le h2 (not_le.mp h118).le h129
      · -- right
        exact CKLaneC2R.Cells.S02.B014.c295_pos (not_le.mp h94).le h2 (not_le.mp h129).le h128
    · -- right
      by_cases h130 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B015.c301_pos (not_le.mp h94).le h2 (not_le.mp h128).le h130
      · -- right
        exact CKLaneC2R.Cells.S02.B015.c303_pos (not_le.mp h94).le h2 (not_le.mp h130).le h117

end CKLaneC2R.CompactCover


