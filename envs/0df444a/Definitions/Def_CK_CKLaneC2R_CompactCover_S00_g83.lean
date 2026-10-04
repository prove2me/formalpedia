-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g83
-- name    : CK_CKLaneC2R_CompactCover_S00_g83
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T03:47:15.366973+00:00
-- url     : https://prove2.me/theorems/30f49bbd-2439-4206-8fcc-0859f408b4bc
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (proof part of strip0) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00 (proof part of strip0).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B000

namespace CKLaneC2R.CompactCover

theorem strip0_s102 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : z ≤ ((217/400 : ℚ) : ℝ)) (h1079 : a ≤ ((59/320 : ℚ) : ℝ)) (h1080 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1110 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h1111 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1112 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1113 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B013.c273_pos (not_le.mp h892).le h1079 (not_le.mp h1080).le h1113
        · -- right
          exact CKLaneC2R.Cells.S00.B013.c274_pos (not_le.mp h892).le h1079 (not_le.mp h1113).le h1112
      · -- right
        by_cases h1114 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B013.c277_pos (not_le.mp h892).le h1079 (not_le.mp h1112).le h1114
        · -- right
          exact CKLaneC2R.Cells.S00.B013.c278_pos (not_le.mp h892).le h1079 (not_le.mp h1114).le h1111
    · -- right
      by_cases h1115 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h1116 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B014.c289_pos (not_le.mp h892).le h1079 (not_le.mp h1111).le h1116
        · -- right
          exact CKLaneC2R.Cells.S00.B014.c290_pos (not_le.mp h892).le h1079 (not_le.mp h1116).le h1115
      · -- right
        by_cases h1117 : z ≤ ((26503/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B014.c293_pos (not_le.mp h892).le h1079 (not_le.mp h1115).le h1117
        · -- right
          exact CKLaneC2R.Cells.S00.B014.c294_pos (not_le.mp h892).le h1079 (not_le.mp h1117).le h1110
  · -- right
    by_cases h1118 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1119 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1120 : z ≤ ((28329/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B016.c329_pos (not_le.mp h892).le h1079 (not_le.mp h1110).le h1120
        · -- right
          exact CKLaneC2R.Cells.S00.B016.c330_pos (not_le.mp h892).le h1079 (not_le.mp h1120).le h1119
      · -- right
        by_cases h1121 : z ≤ ((6031/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B016.c333_pos (not_le.mp h892).le h1079 (not_le.mp h1119).le h1121
        · -- right
          exact CKLaneC2R.Cells.S00.B016.c334_pos (not_le.mp h892).le h1079 (not_le.mp h1121).le h1118
    · -- right
      by_cases h1122 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1123 : z ≤ ((31981/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B017.c343_pos (not_le.mp h892).le h1079 (not_le.mp h1118).le h1123
        · -- right
          exact CKLaneC2R.Cells.S00.B017.c344_pos (not_le.mp h892).le h1079 (not_le.mp h1123).le h1122
      · -- right
        exact CKLaneC2R.Cells.S00.B000.c6_pos (not_le.mp h892).le h1079 (not_le.mp h1122).le h1078

end CKLaneC2R.CompactCover


