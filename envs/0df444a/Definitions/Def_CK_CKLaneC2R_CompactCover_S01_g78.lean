-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g78
-- name    : CK_CKLaneC2R_CompactCover_S01_g78
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T16:12:53.115888+00:00
-- url     : https://prove2.me/theorems/1f9bf9db-d20d-46a2-b658-951ac2d154f5
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B042
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B017

namespace CKLaneC2R.CompactCover

theorem strip1_s114 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : ¬ (a ≤ ((23/80 : ℚ) : ℝ))) (h1106 : z ≤ ((217/400 : ℚ) : ℝ)) (h1107 : a ≤ ((47/160 : ℚ) : ℝ)) (h1108 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1109 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1110 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h1111 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h1112 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1113 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B041.c832_pos (not_le.mp h998).le h1107 hz1 h1113
        · -- right
          exact CKLaneC2R.Cells.S01.B041.c833_pos (not_le.mp h998).le h1107 (not_le.mp h1113).le h1112
      · -- right
        by_cases h1114 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B041.c836_pos (not_le.mp h998).le h1107 (not_le.mp h1112).le h1114
        · -- right
          exact CKLaneC2R.Cells.S01.B041.c837_pos (not_le.mp h998).le h1107 (not_le.mp h1114).le h1111
    · -- right
      by_cases h1115 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1116 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B042.c848_pos (not_le.mp h998).le h1107 (not_le.mp h1111).le h1116
        · -- right
          exact CKLaneC2R.Cells.S01.B042.c849_pos (not_le.mp h998).le h1107 (not_le.mp h1116).le h1115
      · -- right
        exact CKLaneC2R.Cells.S01.B016.c330_pos (not_le.mp h998).le h1107 (not_le.mp h1115).le h1110
  · -- right
    by_cases h1117 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1118 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B017.c340_pos (not_le.mp h998).le h1107 (not_le.mp h1110).le h1118
      · -- right
        exact CKLaneC2R.Cells.S01.B017.c341_pos (not_le.mp h998).le h1107 (not_le.mp h1118).le h1117
    · -- right
      by_cases h1119 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B017.c344_pos (not_le.mp h998).le h1107 (not_le.mp h1117).le h1119
      · -- right
        exact CKLaneC2R.Cells.S01.B017.c345_pos (not_le.mp h998).le h1107 (not_le.mp h1119).le h1109

end CKLaneC2R.CompactCover


