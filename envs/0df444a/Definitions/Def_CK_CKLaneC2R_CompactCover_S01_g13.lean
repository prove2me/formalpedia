-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g13
-- name    : CK_CKLaneC2R_CompactCover_S01_g13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T16:42:50.51218+00:00
-- url     : https://prove2.me/theorems/8a9b397a-11ae-4e89-8ab3-b2732238a9d7
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B012

namespace CKLaneC2R.CompactCover

theorem strip1_s015 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((33/160 : ℚ) : ℝ))) (h118 : z ≤ ((217/400 : ℚ) : ℝ)) (h119 : ¬ (a ≤ ((67/320 : ℚ) : ℝ))) (h148 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h149 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h161 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h162 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h163 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B033.c672_pos (not_le.mp h119).le h2 (not_le.mp h149).le h163
      · -- right
        exact CKLaneC2R.Cells.S01.B033.c674_pos (not_le.mp h119).le h2 (not_le.mp h163).le h162
    · -- right
      by_cases h164 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B033.c677_pos (not_le.mp h119).le h2 (not_le.mp h162).le h164
      · -- right
        exact CKLaneC2R.Cells.S01.B033.c678_pos (not_le.mp h119).le h2 (not_le.mp h164).le h161
  · -- right
    by_cases h165 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h166 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B034.c689_pos (not_le.mp h119).le h2 (not_le.mp h161).le h166
      · -- right
        exact CKLaneC2R.Cells.S01.B034.c690_pos (not_le.mp h119).le h2 (not_le.mp h166).le h165
    · -- right
      by_cases h167 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B034.c693_pos (not_le.mp h119).le h2 (not_le.mp h165).le h167
      · -- right
        exact CKLaneC2R.Cells.S01.B034.c694_pos (not_le.mp h119).le h2 (not_le.mp h167).le h148

theorem strip1_s016 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((33/160 : ℚ) : ℝ))) (h118 : z ≤ ((217/400 : ℚ) : ℝ)) (h119 : ¬ (a ≤ ((67/320 : ℚ) : ℝ))) (h148 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h168 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h169 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h170 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B010.c211_pos (not_le.mp h119).le h2 (not_le.mp h148).le h170
      · -- right
        exact CKLaneC2R.Cells.S01.B010.c213_pos (not_le.mp h119).le h2 (not_le.mp h170).le h169
    · -- right
      by_cases h171 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B010.c219_pos (not_le.mp h119).le h2 (not_le.mp h169).le h171
      · -- right
        exact CKLaneC2R.Cells.S01.B011.c221_pos (not_le.mp h119).le h2 (not_le.mp h171).le h168
  · -- right
    by_cases h172 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h173 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B012.c243_pos (not_le.mp h119).le h2 (not_le.mp h168).le h173
      · -- right
        exact CKLaneC2R.Cells.S01.B012.c245_pos (not_le.mp h119).le h2 (not_le.mp h173).le h172
    · -- right
      by_cases h174 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B012.c251_pos (not_le.mp h119).le h2 (not_le.mp h172).le h174
      · -- right
        exact CKLaneC2R.Cells.S01.B012.c253_pos (not_le.mp h119).le h2 (not_le.mp h174).le h118

end CKLaneC2R.CompactCover


