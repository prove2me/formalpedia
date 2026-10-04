-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g80
-- name    : CK_CKLaneC2R_CompactCover_S01_g80
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T05:48:51.805152+00:00
-- url     : https://prove2.me/theorems/46f8f94e-878b-431f-b94b-ae935f2dc4cc
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

theorem strip1_s117 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : ¬ (a ≤ ((23/80 : ℚ) : ℝ))) (h1106 : z ≤ ((217/400 : ℚ) : ℝ)) (h1107 : ¬ (a ≤ ((47/160 : ℚ) : ℝ))) (h1132 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1133 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1134 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h1135 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h1136 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1137 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B041.c834_pos (not_le.mp h1107).le ha2 hz1 h1137
        · -- right
          exact CKLaneC2R.Cells.S01.B041.c835_pos (not_le.mp h1107).le ha2 (not_le.mp h1137).le h1136
      · -- right
        by_cases h1138 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B041.c838_pos (not_le.mp h1107).le ha2 (not_le.mp h1136).le h1138
        · -- right
          exact CKLaneC2R.Cells.S01.B041.c839_pos (not_le.mp h1107).le ha2 (not_le.mp h1138).le h1135
    · -- right
      by_cases h1139 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1140 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B042.c850_pos (not_le.mp h1107).le ha2 (not_le.mp h1135).le h1140
        · -- right
          exact CKLaneC2R.Cells.S01.B042.c851_pos (not_le.mp h1107).le ha2 (not_le.mp h1140).le h1139
      · -- right
        exact CKLaneC2R.Cells.S01.B016.c331_pos (not_le.mp h1107).le ha2 (not_le.mp h1139).le h1134
  · -- right
    by_cases h1141 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1142 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B017.c342_pos (not_le.mp h1107).le ha2 (not_le.mp h1134).le h1142
      · -- right
        exact CKLaneC2R.Cells.S01.B017.c343_pos (not_le.mp h1107).le ha2 (not_le.mp h1142).le h1141
    · -- right
      by_cases h1143 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B017.c346_pos (not_le.mp h1107).le ha2 (not_le.mp h1141).le h1143
      · -- right
        exact CKLaneC2R.Cells.S01.B017.c347_pos (not_le.mp h1107).le ha2 (not_le.mp h1143).le h1133

end CKLaneC2R.CompactCover


