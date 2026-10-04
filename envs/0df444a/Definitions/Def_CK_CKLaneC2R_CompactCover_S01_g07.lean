-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g07
-- name    : CK_CKLaneC2R_CompactCover_S01_g07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T03:16:58.517358+00:00
-- url     : https://prove2.me/theorems/d74670c4-4da2-4d9b-8582-880d09269f64
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B024
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B025
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B042
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B043

namespace CKLaneC2R.CompactCover

theorem strip1_s007 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : a ≤ ((33/160 : ℚ) : ℝ)) (h4 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h66 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h82 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h83 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h84 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h85 : a ≤ ((13/64 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B024.c498_pos ha1 h85 (not_le.mp h66).le h84
      · -- right
        exact CKLaneC2R.Cells.S01.B024.c499_pos (not_le.mp h85).le h3 (not_le.mp h66).le h84
    · -- right
      by_cases h86 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B025.c502_pos ha1 h3 (not_le.mp h84).le h86
      · -- right
        exact CKLaneC2R.Cells.S01.B025.c503_pos ha1 h3 (not_le.mp h86).le h83
  · -- right
    by_cases h87 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h88 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B025.c514_pos ha1 h3 (not_le.mp h83).le h88
      · -- right
        exact CKLaneC2R.Cells.S01.B025.c515_pos ha1 h3 (not_le.mp h88).le h87
    · -- right
      by_cases h89 : a ≤ ((13/64 : ℚ) : ℝ)
      · -- left
        by_cases h90 : z ≤ ((55719/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B042.c852_pos ha1 h89 (not_le.mp h87).le h90
        · -- right
          exact CKLaneC2R.Cells.S01.B042.c854_pos ha1 h89 (not_le.mp h90).le h82
      · -- right
        by_cases h91 : z ≤ ((55719/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B042.c853_pos (not_le.mp h89).le h3 (not_le.mp h87).le h91
        · -- right
          exact CKLaneC2R.Cells.S01.B042.c855_pos (not_le.mp h89).le h3 (not_le.mp h91).le h82

theorem strip1_s008 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : a ≤ ((33/160 : ℚ) : ℝ)) (h4 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h66 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h82 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h92 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h93 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h94 : a ≤ ((13/64 : ℚ) : ℝ)
    · -- left
      by_cases h95 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B042.c856_pos ha1 h94 (not_le.mp h82).le h95
      · -- right
        exact CKLaneC2R.Cells.S01.B042.c858_pos ha1 h94 (not_le.mp h95).le h93
    · -- right
      by_cases h96 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B042.c857_pos (not_le.mp h94).le h3 (not_le.mp h82).le h96
      · -- right
        exact CKLaneC2R.Cells.S01.B042.c859_pos (not_le.mp h94).le h3 (not_le.mp h96).le h93
  · -- right
    by_cases h97 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      by_cases h98 : a ≤ ((13/64 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B043.c864_pos ha1 h98 (not_le.mp h93).le h97
      · -- right
        exact CKLaneC2R.Cells.S01.B043.c865_pos (not_le.mp h98).le h3 (not_le.mp h93).le h97
    · -- right
      by_cases h99 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B043.c868_pos ha1 h3 (not_le.mp h97).le h99
      · -- right
        exact CKLaneC2R.Cells.S01.B043.c869_pos ha1 h3 (not_le.mp h99).le h92

end CKLaneC2R.CompactCover


