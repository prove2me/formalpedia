-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g03
-- name    : CK_CKLaneC2R_CompactCover_S03_g03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T17:09:22.990702+00:00
-- url     : https://prove2.me/theorems/71fb5369-dfde-4944-b669-56201fa5d6ec
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
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B004

namespace CKLaneC2R.CompactCover

theorem strip3_s005 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : a ≤ ((11/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((21/40 : ℚ) : ℝ))) (h63 : z ≤ ((217/400 : ℚ) : ℝ)) (h64 : a ≤ ((43/80 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h65 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h66 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h67 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h68 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h69 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B015.c310_pos (not_le.mp h2).le h64 hz1 h69
          · -- right
            exact CKLaneC2R.Cells.S03.B015.c311_pos (not_le.mp h2).le h64 (not_le.mp h69).le h68
        · -- right
          by_cases h70 : z ≤ ((8243/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B015.c314_pos (not_le.mp h2).le h64 (not_le.mp h68).le h70
          · -- right
            exact CKLaneC2R.Cells.S03.B015.c315_pos (not_le.mp h2).le h64 (not_le.mp h70).le h67
      · -- right
        by_cases h71 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B008.c176_pos (not_le.mp h2).le h64 (not_le.mp h67).le h71
        · -- right
          exact CKLaneC2R.Cells.S03.B008.c178_pos (not_le.mp h2).le h64 (not_le.mp h71).le h66
    · -- right
      by_cases h72 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        by_cases h73 : z ≤ ((7317/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B010.c200_pos (not_le.mp h2).le h64 (not_le.mp h66).le h73
        · -- right
          exact CKLaneC2R.Cells.S03.B010.c202_pos (not_le.mp h2).le h64 (not_le.mp h73).le h72
      · -- right
        by_cases h74 : z ≤ ((9143/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B010.c204_pos (not_le.mp h2).le h64 (not_le.mp h72).le h74
        · -- right
          exact CKLaneC2R.Cells.S03.B010.c205_pos (not_le.mp h2).le h64 (not_le.mp h74).le h65
  · -- right
    by_cases h75 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h76 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B000.c6_pos (not_le.mp h2).le h64 (not_le.mp h65).le h76
      · -- right
        exact CKLaneC2R.Cells.S03.B000.c8_pos (not_le.mp h2).le h64 (not_le.mp h76).le h75
    · -- right
      by_cases h77 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B000.c14_pos (not_le.mp h2).le h64 (not_le.mp h75).le h77
      · -- right
        exact CKLaneC2R.Cells.S03.B000.c16_pos (not_le.mp h2).le h64 (not_le.mp h77).le h63

theorem strip3_s006 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : a ≤ ((11/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((21/40 : ℚ) : ℝ))) (h63 : z ≤ ((217/400 : ℚ) : ℝ)) (h64 : ¬ (a ≤ ((43/80 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h78 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h79 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h80 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h81 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h82 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B015.c312_pos (not_le.mp h64).le h1 hz1 h82
          · -- right
            exact CKLaneC2R.Cells.S03.B015.c313_pos (not_le.mp h64).le h1 (not_le.mp h82).le h81
        · -- right
          by_cases h83 : z ≤ ((8243/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B015.c316_pos (not_le.mp h64).le h1 (not_le.mp h81).le h83
          · -- right
            exact CKLaneC2R.Cells.S03.B015.c317_pos (not_le.mp h64).le h1 (not_le.mp h83).le h80
      · -- right
        by_cases h84 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B008.c177_pos (not_le.mp h64).le h1 (not_le.mp h80).le h84
        · -- right
          exact CKLaneC2R.Cells.S03.B008.c179_pos (not_le.mp h64).le h1 (not_le.mp h84).le h79
    · -- right
      by_cases h85 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        by_cases h86 : z ≤ ((7317/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B010.c201_pos (not_le.mp h64).le h1 (not_le.mp h79).le h86
        · -- right
          exact CKLaneC2R.Cells.S03.B010.c203_pos (not_le.mp h64).le h1 (not_le.mp h86).le h85
      · -- right
        by_cases h87 : z ≤ ((9143/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B010.c206_pos (not_le.mp h64).le h1 (not_le.mp h85).le h87
        · -- right
          exact CKLaneC2R.Cells.S03.B010.c207_pos (not_le.mp h64).le h1 (not_le.mp h87).le h78
  · -- right
    by_cases h88 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h89 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B000.c7_pos (not_le.mp h64).le h1 (not_le.mp h78).le h89
      · -- right
        exact CKLaneC2R.Cells.S03.B000.c9_pos (not_le.mp h64).le h1 (not_le.mp h89).le h88
    · -- right
      by_cases h90 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B000.c15_pos (not_le.mp h64).le h1 (not_le.mp h88).le h90
      · -- right
        exact CKLaneC2R.Cells.S03.B000.c17_pos (not_le.mp h64).le h1 (not_le.mp h90).le h63

theorem strip3_s007 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : a ≤ ((11/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((21/40 : ℚ) : ℝ))) (h63 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h91 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h92 : a ≤ ((43/80 : ℚ) : ℝ)
  · -- left
    by_cases h93 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h94 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B004.c87_pos (not_le.mp h2).le h92 (not_le.mp h63).le h94
      · -- right
        exact CKLaneC2R.Cells.S03.B004.c89_pos (not_le.mp h2).le h92 (not_le.mp h94).le h93
    · -- right
      by_cases h95 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B004.c95_pos (not_le.mp h2).le h92 (not_le.mp h93).le h95
      · -- right
        exact CKLaneC2R.Cells.S03.B004.c97_pos (not_le.mp h2).le h92 (not_le.mp h95).le h91
  · -- right
    by_cases h96 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h97 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B004.c88_pos (not_le.mp h92).le h1 (not_le.mp h63).le h97
      · -- right
        exact CKLaneC2R.Cells.S03.B004.c90_pos (not_le.mp h92).le h1 (not_le.mp h97).le h96
    · -- right
      by_cases h98 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B004.c96_pos (not_le.mp h92).le h1 (not_le.mp h96).le h98
      · -- right
        exact CKLaneC2R.Cells.S03.B004.c98_pos (not_le.mp h92).le h1 (not_le.mp h98).le h91

end CKLaneC2R.CompactCover


