-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g09
-- name    : CK_CKLaneC2R_CompactCover_S01_g09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T12:58:27.242363+00:00
-- url     : https://prove2.me/theorems/3b311c93-e4c0-4244-8408-02b7d4dad667
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B053
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B054
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B056
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B060

namespace CKLaneC2R.CompactCover

theorem strip1_s010 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : a ≤ ((33/160 : ℚ) : ℝ)) (h4 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h66 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h82 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h92 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h100 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h105 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h106 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      by_cases h107 : a ≤ ((13/64 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B053.c1074_pos ha1 h107 (not_le.mp h100).le h106
      · -- right
        exact CKLaneC2R.Cells.S01.B053.c1075_pos (not_le.mp h107).le h3 (not_le.mp h100).le h106
    · -- right
      by_cases h108 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B053.c1078_pos ha1 h3 (not_le.mp h106).le h108
      · -- right
        exact CKLaneC2R.Cells.S01.B053.c1079_pos ha1 h3 (not_le.mp h108).le h105
  · -- right
    by_cases h109 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h110 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B054.c1094_pos ha1 h3 (not_le.mp h105).le h110
      · -- right
        by_cases h111 : a ≤ ((13/64 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B056.c1133_pos ha1 h111 (not_le.mp h110).le h109
        · -- right
          exact CKLaneC2R.Cells.S01.B056.c1134_pos (not_le.mp h111).le h3 (not_le.mp h110).le h109
    · -- right
      by_cases h112 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h113 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B056.c1137_pos ha1 h3 (not_le.mp h109).le h113
        · -- right
          exact CKLaneC2R.Cells.S01.B056.c1138_pos ha1 h3 (not_le.mp h113).le h112
      · -- right
        by_cases h114 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          by_cases h115 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B058.c1172_pos ha1 h3 (not_le.mp h112).le h115
          · -- right
            exact CKLaneC2R.Cells.S01.B058.c1173_pos ha1 h3 (not_le.mp h115).le h114
        · -- right
          by_cases h116 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B058.c1176_pos ha1 h3 (not_le.mp h114).le h116
          · -- right
            by_cases h117 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B060.c1200_pos ha1 h3 (not_le.mp h116).le h117
            · -- right
              exact CKLaneC2R.Cells.S01.B060.c1201_pos ha1 h3 (not_le.mp h117).le hz2

end CKLaneC2R.CompactCover


