-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g11
-- name    : CK_CKLaneC2R_CompactCover_S01_g11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T13:24:30.78076+00:00
-- url     : https://prove2.me/theorems/c4797bc9-b0a1-4e3d-869e-16cd9c672a3c
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

theorem strip1_s012 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((33/160 : ℚ) : ℝ))) (h118 : z ≤ ((217/400 : ℚ) : ℝ)) (h119 : a ≤ ((67/320 : ℚ) : ℝ)) (h120 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h121 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h134 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h135 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h136 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B033.c671_pos (not_le.mp h3).le h119 (not_le.mp h121).le h136
      · -- right
        exact CKLaneC2R.Cells.S01.B033.c673_pos (not_le.mp h3).le h119 (not_le.mp h136).le h135
    · -- right
      by_cases h137 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B033.c675_pos (not_le.mp h3).le h119 (not_le.mp h135).le h137
      · -- right
        exact CKLaneC2R.Cells.S01.B033.c676_pos (not_le.mp h3).le h119 (not_le.mp h137).le h134
  · -- right
    by_cases h138 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h139 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B034.c687_pos (not_le.mp h3).le h119 (not_le.mp h134).le h139
      · -- right
        exact CKLaneC2R.Cells.S01.B034.c688_pos (not_le.mp h3).le h119 (not_le.mp h139).le h138
    · -- right
      by_cases h140 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B034.c691_pos (not_le.mp h3).le h119 (not_le.mp h138).le h140
      · -- right
        exact CKLaneC2R.Cells.S01.B034.c692_pos (not_le.mp h3).le h119 (not_le.mp h140).le h120

theorem strip1_s013 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((33/160 : ℚ) : ℝ))) (h118 : z ≤ ((217/400 : ℚ) : ℝ)) (h119 : a ≤ ((67/320 : ℚ) : ℝ)) (h120 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h141 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h142 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h143 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B010.c210_pos (not_le.mp h3).le h119 (not_le.mp h120).le h143
      · -- right
        exact CKLaneC2R.Cells.S01.B010.c212_pos (not_le.mp h3).le h119 (not_le.mp h143).le h142
    · -- right
      by_cases h144 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B010.c218_pos (not_le.mp h3).le h119 (not_le.mp h142).le h144
      · -- right
        exact CKLaneC2R.Cells.S01.B011.c220_pos (not_le.mp h3).le h119 (not_le.mp h144).le h141
  · -- right
    by_cases h145 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h146 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B012.c242_pos (not_le.mp h3).le h119 (not_le.mp h141).le h146
      · -- right
        exact CKLaneC2R.Cells.S01.B012.c244_pos (not_le.mp h3).le h119 (not_le.mp h146).le h145
    · -- right
      by_cases h147 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B012.c250_pos (not_le.mp h3).le h119 (not_le.mp h145).le h147
      · -- right
        exact CKLaneC2R.Cells.S01.B012.c252_pos (not_le.mp h3).le h119 (not_le.mp h147).le h118

end CKLaneC2R.CompactCover


