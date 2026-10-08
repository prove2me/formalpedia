-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g81
-- name    : CK_CKLaneC2R_CompactCover_S01_g81
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T12:14:57.504985+00:00
-- url     : https://prove2.me/theorems/2e6eeb64-9c43-4f59-bd4e-dd84d625a2ea
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B003

namespace CKLaneC2R.CompactCover

theorem strip1_s118 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : ¬ (a ≤ ((23/80 : ℚ) : ℝ))) (h1106 : z ≤ ((217/400 : ℚ) : ℝ)) (h1107 : ¬ (a ≤ ((47/160 : ℚ) : ℝ))) (h1132 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1133 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1144 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h1145 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1146 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B019.c390_pos (not_le.mp h1107).le ha2 (not_le.mp h1133).le h1146
      · -- right
        exact CKLaneC2R.Cells.S01.B019.c391_pos (not_le.mp h1107).le ha2 (not_le.mp h1146).le h1145
    · -- right
      by_cases h1147 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B019.c394_pos (not_le.mp h1107).le ha2 (not_le.mp h1145).le h1147
      · -- right
        exact CKLaneC2R.Cells.S01.B019.c395_pos (not_le.mp h1107).le ha2 (not_le.mp h1147).le h1144
  · -- right
    by_cases h1148 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B000.c9_pos (not_le.mp h1107).le ha2 (not_le.mp h1144).le h1148
    · -- right
      exact CKLaneC2R.Cells.S01.B000.c11_pos (not_le.mp h1107).le ha2 (not_le.mp h1148).le h1132

theorem strip1_s119 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : ¬ (a ≤ ((23/80 : ℚ) : ℝ))) (h1106 : z ≤ ((217/400 : ℚ) : ℝ)) (h1107 : ¬ (a ≤ ((47/160 : ℚ) : ℝ))) (h1132 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1149 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h1150 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1151 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B002.c48_pos (not_le.mp h1107).le ha2 (not_le.mp h1132).le h1151
      · -- right
        exact CKLaneC2R.Cells.S01.B002.c50_pos (not_le.mp h1107).le ha2 (not_le.mp h1151).le h1150
    · -- right
      by_cases h1152 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B002.c52_pos (not_le.mp h1107).le ha2 (not_le.mp h1150).le h1152
      · -- right
        exact CKLaneC2R.Cells.S01.B002.c54_pos (not_le.mp h1107).le ha2 (not_le.mp h1152).le h1149
  · -- right
    by_cases h1153 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1154 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B003.c64_pos (not_le.mp h1107).le ha2 (not_le.mp h1149).le h1154
      · -- right
        exact CKLaneC2R.Cells.S01.B003.c66_pos (not_le.mp h1107).le ha2 (not_le.mp h1154).le h1153
    · -- right
      by_cases h1155 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B003.c68_pos (not_le.mp h1107).le ha2 (not_le.mp h1153).le h1155
      · -- right
        exact CKLaneC2R.Cells.S01.B003.c70_pos (not_le.mp h1107).le ha2 (not_le.mp h1155).le h1106

end CKLaneC2R.CompactCover


