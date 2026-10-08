-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g06
-- name    : CK_CKLaneC2R_CompactCover_S03_g06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T12:24:39.879896+00:00
-- url     : https://prove2.me/theorems/9a891b4f-6efd-448f-813e-4d707bf34c81
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S03 (proof part of strip3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S03 (proof part of strip3).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B015
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B000

namespace CKLaneC2R.CompactCover

theorem strip3_s010 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((11/20 : ℚ) : ℝ))) (h119 : a ≤ ((23/40 : ℚ) : ℝ)) (h120 : z ≤ ((217/400 : ℚ) : ℝ)) (h121 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h122 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h123 : a ≤ ((9/16 : ℚ) : ℝ)
    · -- left
      by_cases h124 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h125 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h126 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B015.c318_pos (not_le.mp h1).le h123 hz1 h126
          · -- right
            exact CKLaneC2R.Cells.S03.B016.c320_pos (not_le.mp h1).le h123 (not_le.mp h126).le h125
        · -- right
          exact CKLaneC2R.Cells.S03.B009.c180_pos (not_le.mp h1).le h123 (not_le.mp h125).le h124
      · -- right
        by_cases h127 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B009.c184_pos (not_le.mp h1).le h123 (not_le.mp h124).le h127
        · -- right
          exact CKLaneC2R.Cells.S03.B009.c186_pos (not_le.mp h1).le h123 (not_le.mp h127).le h122
    · -- right
      by_cases h128 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h129 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h130 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B015.c319_pos (not_le.mp h123).le h119 hz1 h130
          · -- right
            exact CKLaneC2R.Cells.S03.B016.c321_pos (not_le.mp h123).le h119 (not_le.mp h130).le h129
        · -- right
          exact CKLaneC2R.Cells.S03.B009.c181_pos (not_le.mp h123).le h119 (not_le.mp h129).le h128
      · -- right
        by_cases h131 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B009.c185_pos (not_le.mp h123).le h119 (not_le.mp h128).le h131
        · -- right
          exact CKLaneC2R.Cells.S03.B009.c187_pos (not_le.mp h123).le h119 (not_le.mp h131).le h122
  · -- right
    by_cases h132 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h133 : a ≤ ((9/16 : ℚ) : ℝ)
      · -- left
        by_cases h134 : z ≤ ((7317/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B010.c208_pos (not_le.mp h1).le h133 (not_le.mp h122).le h134
        · -- right
          exact CKLaneC2R.Cells.S03.B010.c210_pos (not_le.mp h1).le h133 (not_le.mp h134).le h132
      · -- right
        by_cases h135 : z ≤ ((7317/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B010.c209_pos (not_le.mp h133).le h119 (not_le.mp h122).le h135
        · -- right
          exact CKLaneC2R.Cells.S03.B010.c211_pos (not_le.mp h133).le h119 (not_le.mp h135).le h132
    · -- right
      by_cases h136 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        by_cases h137 : a ≤ ((9/16 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B010.c216_pos (not_le.mp h1).le h137 (not_le.mp h132).le h136
        · -- right
          exact CKLaneC2R.Cells.S03.B010.c217_pos (not_le.mp h137).le h119 (not_le.mp h132).le h136
      · -- right
        exact CKLaneC2R.Cells.S03.B000.c0_pos (not_le.mp h1).le h119 (not_le.mp h136).le h121

end CKLaneC2R.CompactCover


