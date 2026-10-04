-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g80
-- name    : CK_CKLaneC2R_CompactCover_S00_g80
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T04:23:57.076232+00:00
-- url     : https://prove2.me/theorems/c7e063f3-c87a-4ddf-9f44-3afcdef56dae
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B051
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B052
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B066
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B067
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B071
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B072
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B074
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B075

namespace CKLaneC2R.CompactCover

theorem strip0_s098 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : ¬ (a ≤ ((57/320 : ℚ) : ℝ))) (h988 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1035 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1051 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1059 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1064 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h1065 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1066 : z ≤ ((121481/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B051.c1023_pos (not_le.mp h893).le h892 (not_le.mp h1059).le h1066
      · -- right
        exact CKLaneC2R.Cells.S00.B051.c1025_pos (not_le.mp h893).le h892 (not_le.mp h1066).le h1065
    · -- right
      by_cases h1067 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B051.c1031_pos (not_le.mp h893).le h892 (not_le.mp h1065).le h1067
      · -- right
        exact CKLaneC2R.Cells.S00.B051.c1033_pos (not_le.mp h893).le h892 (not_le.mp h1067).le h1064
  · -- right
    by_cases h1068 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1069 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B052.c1050_pos (not_le.mp h893).le h892 (not_le.mp h1064).le h1069
      · -- right
        by_cases h1070 : z ≤ ((251179/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B066.c1334_pos (not_le.mp h893).le h892 (not_le.mp h1069).le h1070
        · -- right
          exact CKLaneC2R.Cells.S00.B066.c1336_pos (not_le.mp h893).le h892 (not_le.mp h1070).le h1068
    · -- right
      by_cases h1071 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h1072 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B067.c1352_pos (not_le.mp h893).le h892 (not_le.mp h1068).le h1072
        · -- right
          exact CKLaneC2R.Cells.S00.B067.c1354_pos (not_le.mp h893).le h892 (not_le.mp h1072).le h1071
      · -- right
        by_cases h1073 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          by_cases h1074 : z ≤ ((508749/512000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B071.c1437_pos (not_le.mp h893).le h892 (not_le.mp h1071).le h1074
          · -- right
            exact CKLaneC2R.Cells.S00.B071.c1439_pos (not_le.mp h893).le h892 (not_le.mp h1074).le h1073
        · -- right
          by_cases h1075 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B072.c1447_pos (not_le.mp h893).le h892 (not_le.mp h1073).le h1075
          · -- right
            by_cases h1076 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S00.B074.c1481_pos (not_le.mp h893).le h892 (not_le.mp h1075).le h1076
            · -- right
              by_cases h1077 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S00.B075.c1507_pos (not_le.mp h893).le h892 (not_le.mp h1076).le h1077
              · -- right
                exact CKLaneC2R.Cells.S00.B075.c1509_pos (not_le.mp h893).le h892 (not_le.mp h1077).le hz2

end CKLaneC2R.CompactCover


