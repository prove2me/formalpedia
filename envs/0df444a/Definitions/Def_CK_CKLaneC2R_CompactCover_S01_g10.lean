-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g10
-- name    : CK_CKLaneC2R_CompactCover_S01_g10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T12:32:57.328551+00:00
-- url     : https://prove2.me/theorems/a1771a4e-d0d5-431f-8918-a157e9e8061e
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
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B050
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B032

namespace CKLaneC2R.CompactCover

theorem strip1_s011 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((33/160 : ℚ) : ℝ))) (h118 : z ≤ ((217/400 : ℚ) : ℝ)) (h119 : a ≤ ((67/320 : ℚ) : ℝ)) (h120 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h121 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h122 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h123 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h124 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h125 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B047.c956_pos (not_le.mp h3).le h119 hz1 h125
        · -- right
          exact CKLaneC2R.Cells.S01.B047.c957_pos (not_le.mp h3).le h119 (not_le.mp h125).le h124
      · -- right
        by_cases h126 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B048.c960_pos (not_le.mp h3).le h119 (not_le.mp h124).le h126
        · -- right
          exact CKLaneC2R.Cells.S01.B048.c961_pos (not_le.mp h3).le h119 (not_le.mp h126).le h123
    · -- right
      by_cases h127 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h128 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B048.c972_pos (not_le.mp h3).le h119 (not_le.mp h123).le h128
        · -- right
          exact CKLaneC2R.Cells.S01.B048.c973_pos (not_le.mp h3).le h119 (not_le.mp h128).le h127
      · -- right
        by_cases h129 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B048.c976_pos (not_le.mp h3).le h119 (not_le.mp h127).le h129
        · -- right
          exact CKLaneC2R.Cells.S01.B048.c977_pos (not_le.mp h3).le h119 (not_le.mp h129).le h122
  · -- right
    by_cases h130 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h131 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        by_cases h132 : z ≤ ((769/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B050.c1012_pos (not_le.mp h3).le h119 (not_le.mp h122).le h132
        · -- right
          exact CKLaneC2R.Cells.S01.B050.c1013_pos (not_le.mp h3).le h119 (not_le.mp h132).le h131
      · -- right
        exact CKLaneC2R.Cells.S01.B031.c637_pos (not_le.mp h3).le h119 (not_le.mp h131).le h130
    · -- right
      by_cases h133 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B032.c643_pos (not_le.mp h3).le h119 (not_le.mp h130).le h133
      · -- right
        exact CKLaneC2R.Cells.S01.B032.c645_pos (not_le.mp h3).le h119 (not_le.mp h133).le h121

end CKLaneC2R.CompactCover


