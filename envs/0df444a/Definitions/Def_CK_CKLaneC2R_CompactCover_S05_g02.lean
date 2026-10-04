-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g02
-- name    : CK_CKLaneC2R_CompactCover_S05_g02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T18:49:03.759728+00:00
-- url     : https://prove2.me/theorems/06fc0c62-9813-470c-8b5e-9ca0ece2b6f2
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

theorem strip5_s003 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : a ≤ ((3699/4000 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((7299/8000 : ℚ) : ℝ))) (h34 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h35 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h36 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h37 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h38 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B002.c49_pos (not_le.mp h2).le h1 hz1 h38
        · -- right
          exact CKLaneC2R.Cells.S05.B002.c51_pos (not_le.mp h2).le h1 (not_le.mp h38).le h37
      · -- right
        exact CKLaneC2R.Cells.S05.B000.c1_pos (not_le.mp h2).le h1 (not_le.mp h37).le h36
    · -- right
      by_cases h39 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B000.c5_pos (not_le.mp h2).le h1 (not_le.mp h36).le h39
      · -- right
        exact CKLaneC2R.Cells.S05.B000.c7_pos (not_le.mp h2).le h1 (not_le.mp h39).le h35
  · -- right
    by_cases h40 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h41 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B000.c13_pos (not_le.mp h2).le h1 (not_le.mp h35).le h41
      · -- right
        exact CKLaneC2R.Cells.S05.B000.c15_pos (not_le.mp h2).le h1 (not_le.mp h41).le h40
    · -- right
      by_cases h42 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B001.c21_pos (not_le.mp h2).le h1 (not_le.mp h40).le h42
      · -- right
        exact CKLaneC2R.Cells.S05.B001.c23_pos (not_le.mp h2).le h1 (not_le.mp h42).le h34

theorem strip5_s004 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : a ≤ ((3699/4000 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((7299/8000 : ℚ) : ℝ))) (h34 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h43 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h44 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h45 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B001.c35_pos (not_le.mp h2).le h1 (not_le.mp h34).le h45
    · -- right
      exact CKLaneC2R.Cells.S05.B001.c37_pos (not_le.mp h2).le h1 (not_le.mp h45).le h44
  · -- right
    by_cases h46 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B002.c43_pos (not_le.mp h2).le h1 (not_le.mp h44).le h46
    · -- right
      by_cases h47 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B004.c93_pos (not_le.mp h2).le h1 (not_le.mp h46).le h47
      · -- right
        exact CKLaneC2R.Cells.S05.B004.c94_pos (not_le.mp h2).le h1 (not_le.mp h47).le h43

end CKLaneC2R.CompactCover


