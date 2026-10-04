-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g06
-- name    : CK_CKLaneC2R_CompactCover_S01_g06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T12:21:49.964984+00:00
-- url     : https://prove2.me/theorems/5157f736-4216-4b1c-9a8c-60634a198fb4
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B021
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B022

namespace CKLaneC2R.CompactCover

theorem strip1_s006 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : a ≤ ((33/160 : ℚ) : ℝ)) (h4 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h66 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h67 : a ≤ ((13/64 : ℚ) : ℝ)
  · -- left
    by_cases h68 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h69 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h70 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B020.c410_pos ha1 h67 (not_le.mp h4).le h70
        · -- right
          exact CKLaneC2R.Cells.S01.B020.c412_pos ha1 h67 (not_le.mp h70).le h69
      · -- right
        by_cases h71 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B020.c418_pos ha1 h67 (not_le.mp h69).le h71
        · -- right
          exact CKLaneC2R.Cells.S01.B021.c420_pos ha1 h67 (not_le.mp h71).le h68
    · -- right
      by_cases h72 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h73 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B022.c442_pos ha1 h67 (not_le.mp h68).le h73
        · -- right
          exact CKLaneC2R.Cells.S01.B022.c444_pos ha1 h67 (not_le.mp h73).le h72
      · -- right
        by_cases h74 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B022.c450_pos ha1 h67 (not_le.mp h72).le h74
        · -- right
          exact CKLaneC2R.Cells.S01.B022.c452_pos ha1 h67 (not_le.mp h74).le h66
  · -- right
    by_cases h75 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h76 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h77 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B020.c411_pos (not_le.mp h67).le h3 (not_le.mp h4).le h77
        · -- right
          exact CKLaneC2R.Cells.S01.B020.c413_pos (not_le.mp h67).le h3 (not_le.mp h77).le h76
      · -- right
        by_cases h78 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B020.c419_pos (not_le.mp h67).le h3 (not_le.mp h76).le h78
        · -- right
          exact CKLaneC2R.Cells.S01.B021.c421_pos (not_le.mp h67).le h3 (not_le.mp h78).le h75
    · -- right
      by_cases h79 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h80 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B022.c443_pos (not_le.mp h67).le h3 (not_le.mp h75).le h80
        · -- right
          exact CKLaneC2R.Cells.S01.B022.c445_pos (not_le.mp h67).le h3 (not_le.mp h80).le h79
      · -- right
        by_cases h81 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B022.c451_pos (not_le.mp h67).le h3 (not_le.mp h79).le h81
        · -- right
          exact CKLaneC2R.Cells.S01.B022.c453_pos (not_le.mp h67).le h3 (not_le.mp h81).le h66

end CKLaneC2R.CompactCover


