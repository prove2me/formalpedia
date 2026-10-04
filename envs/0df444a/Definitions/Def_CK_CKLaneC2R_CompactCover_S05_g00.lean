-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g00
-- name    : CK_CKLaneC2R_CompactCover_S05_g00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T04:34:32.532504+00:00
-- url     : https://prove2.me/theorems/dc8f139f-fe05-458f-a77e-87c1d078b3ad
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S05 (proof part of strip5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S05 (proof part of strip5).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B004

namespace CKLaneC2R.CompactCover

theorem strip5_s000 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : a ≤ ((3699/4000 : ℚ) : ℝ)) (h2 : a ≤ ((7299/8000 : ℚ) : ℝ)) (h3 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h4 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h5 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h6 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h7 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B002.c48_pos ha1 h2 hz1 h7
        · -- right
          exact CKLaneC2R.Cells.S05.B002.c50_pos ha1 h2 (not_le.mp h7).le h6
      · -- right
        exact CKLaneC2R.Cells.S05.B000.c0_pos ha1 h2 (not_le.mp h6).le h5
    · -- right
      by_cases h8 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B000.c4_pos ha1 h2 (not_le.mp h5).le h8
      · -- right
        exact CKLaneC2R.Cells.S05.B000.c6_pos ha1 h2 (not_le.mp h8).le h4
  · -- right
    by_cases h9 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h10 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B000.c12_pos ha1 h2 (not_le.mp h4).le h10
      · -- right
        exact CKLaneC2R.Cells.S05.B000.c14_pos ha1 h2 (not_le.mp h10).le h9
    · -- right
      by_cases h11 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B001.c20_pos ha1 h2 (not_le.mp h9).le h11
      · -- right
        exact CKLaneC2R.Cells.S05.B001.c22_pos ha1 h2 (not_le.mp h11).le h3

theorem strip5_s001 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : a ≤ ((3699/4000 : ℚ) : ℝ)) (h2 : a ≤ ((7299/8000 : ℚ) : ℝ)) (h3 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h12 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h13 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h14 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B001.c34_pos ha1 h2 (not_le.mp h3).le h14
    · -- right
      exact CKLaneC2R.Cells.S05.B001.c36_pos ha1 h2 (not_le.mp h14).le h13
  · -- right
    by_cases h15 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B002.c42_pos ha1 h2 (not_le.mp h13).le h15
    · -- right
      by_cases h16 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B004.c91_pos ha1 h2 (not_le.mp h15).le h16
      · -- right
        exact CKLaneC2R.Cells.S05.B004.c92_pos ha1 h2 (not_le.mp h16).le h12

end CKLaneC2R.CompactCover


