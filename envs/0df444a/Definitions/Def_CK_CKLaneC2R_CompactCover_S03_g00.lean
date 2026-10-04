-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g00
-- name    : CK_CKLaneC2R_CompactCover_S03_g00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T09:47:34.25498+00:00
-- url     : https://prove2.me/theorems/b514eb57-6c5a-4575-9e37-0d9c85c397db
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
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B000

namespace CKLaneC2R.CompactCover

theorem strip3_s000 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : a ≤ ((11/20 : ℚ) : ℝ)) (h2 : a ≤ ((21/40 : ℚ) : ℝ)) (h3 : z ≤ ((217/400 : ℚ) : ℝ)) (h4 : a ≤ ((41/80 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h5 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h6 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h7 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h8 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h9 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B015.c302_pos ha1 h4 hz1 h9
          · -- right
            exact CKLaneC2R.Cells.S03.B015.c303_pos ha1 h4 (not_le.mp h9).le h8
        · -- right
          by_cases h10 : z ≤ ((8243/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B015.c306_pos ha1 h4 (not_le.mp h8).le h10
          · -- right
            exact CKLaneC2R.Cells.S03.B015.c307_pos ha1 h4 (not_le.mp h10).le h7
      · -- right
        by_cases h11 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B008.c172_pos ha1 h4 (not_le.mp h7).le h11
        · -- right
          exact CKLaneC2R.Cells.S03.B008.c174_pos ha1 h4 (not_le.mp h11).le h6
    · -- right
      by_cases h12 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        by_cases h13 : z ≤ ((7317/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B009.c192_pos ha1 h4 (not_le.mp h6).le h13
        · -- right
          exact CKLaneC2R.Cells.S03.B009.c194_pos ha1 h4 (not_le.mp h13).le h12
      · -- right
        by_cases h14 : z ≤ ((9143/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B009.c196_pos ha1 h4 (not_le.mp h12).le h14
        · -- right
          exact CKLaneC2R.Cells.S03.B009.c197_pos ha1 h4 (not_le.mp h14).le h5
  · -- right
    by_cases h15 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h16 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        by_cases h17 : z ≤ ((10969/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B010.c218_pos ha1 h4 (not_le.mp h5).le h17
        · -- right
          exact CKLaneC2R.Cells.S03.B010.c219_pos ha1 h4 (not_le.mp h17).le h16
      · -- right
        exact CKLaneC2R.Cells.S03.B000.c4_pos ha1 h4 (not_le.mp h16).le h15
    · -- right
      by_cases h18 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B000.c10_pos ha1 h4 (not_le.mp h15).le h18
      · -- right
        exact CKLaneC2R.Cells.S03.B000.c12_pos ha1 h4 (not_le.mp h18).le h3

theorem strip3_s001 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : a ≤ ((11/20 : ℚ) : ℝ)) (h2 : a ≤ ((21/40 : ℚ) : ℝ)) (h3 : z ≤ ((217/400 : ℚ) : ℝ)) (h4 : ¬ (a ≤ ((41/80 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h19 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h20 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h21 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h22 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h23 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B015.c304_pos (not_le.mp h4).le h2 hz1 h23
          · -- right
            exact CKLaneC2R.Cells.S03.B015.c305_pos (not_le.mp h4).le h2 (not_le.mp h23).le h22
        · -- right
          by_cases h24 : z ≤ ((8243/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B015.c308_pos (not_le.mp h4).le h2 (not_le.mp h22).le h24
          · -- right
            exact CKLaneC2R.Cells.S03.B015.c309_pos (not_le.mp h4).le h2 (not_le.mp h24).le h21
      · -- right
        by_cases h25 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B008.c173_pos (not_le.mp h4).le h2 (not_le.mp h21).le h25
        · -- right
          exact CKLaneC2R.Cells.S03.B008.c175_pos (not_le.mp h4).le h2 (not_le.mp h25).le h20
    · -- right
      by_cases h26 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        by_cases h27 : z ≤ ((7317/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B009.c193_pos (not_le.mp h4).le h2 (not_le.mp h20).le h27
        · -- right
          exact CKLaneC2R.Cells.S03.B009.c195_pos (not_le.mp h4).le h2 (not_le.mp h27).le h26
      · -- right
        by_cases h28 : z ≤ ((9143/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B009.c198_pos (not_le.mp h4).le h2 (not_le.mp h26).le h28
        · -- right
          exact CKLaneC2R.Cells.S03.B009.c199_pos (not_le.mp h4).le h2 (not_le.mp h28).le h19
  · -- right
    by_cases h29 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h30 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B000.c3_pos (not_le.mp h4).le h2 (not_le.mp h19).le h30
      · -- right
        exact CKLaneC2R.Cells.S03.B000.c5_pos (not_le.mp h4).le h2 (not_le.mp h30).le h29
    · -- right
      by_cases h31 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B000.c11_pos (not_le.mp h4).le h2 (not_le.mp h29).le h31
      · -- right
        exact CKLaneC2R.Cells.S03.B000.c13_pos (not_le.mp h4).le h2 (not_le.mp h31).le h3

end CKLaneC2R.CompactCover


