-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g84
-- name    : CK_CKLaneC2R_CompactCover_S00_g84
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T08:08:58.986166+00:00
-- url     : https://prove2.me/theorems/6b9453c3-bc26-4931-b758-0b623954b986
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B062
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B043
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B044

namespace CKLaneC2R.CompactCover

theorem strip0_s103 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : z ≤ ((217/400 : ℚ) : ℝ)) (h1079 : ¬ (a ≤ ((59/320 : ℚ) : ℝ))) (h1124 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1125 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h1126 : z ≤ ((2289/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1127 : z ≤ ((733/6400 : ℚ) : ℝ)
  · -- left
    by_cases h1128 : a ≤ ((119/640 : ℚ) : ℝ)
    · -- left
      by_cases h1129 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1130 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B062.c1245_pos (not_le.mp h1079).le h1128 hz1 h1130
        · -- right
          exact CKLaneC2R.Cells.S00.B062.c1247_pos (not_le.mp h1079).le h1128 (not_le.mp h1130).le h1129
      · -- right
        by_cases h1131 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B062.c1253_pos (not_le.mp h1079).le h1128 (not_le.mp h1129).le h1131
        · -- right
          exact CKLaneC2R.Cells.S00.B062.c1255_pos (not_le.mp h1079).le h1128 (not_le.mp h1131).le h1127
    · -- right
      by_cases h1132 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h1133 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B062.c1246_pos (not_le.mp h1128).le h891 hz1 h1133
        · -- right
          exact CKLaneC2R.Cells.S00.B062.c1248_pos (not_le.mp h1128).le h891 (not_le.mp h1133).le h1132
      · -- right
        by_cases h1134 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B062.c1254_pos (not_le.mp h1128).le h891 (not_le.mp h1132).le h1134
        · -- right
          exact CKLaneC2R.Cells.S00.B062.c1256_pos (not_le.mp h1128).le h891 (not_le.mp h1134).le h1127
  · -- right
    by_cases h1135 : z ≤ ((8243/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1136 : z ≤ ((15573/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B041.c833_pos (not_le.mp h1079).le h891 (not_le.mp h1127).le h1136
      · -- right
        exact CKLaneC2R.Cells.S00.B041.c834_pos (not_le.mp h1079).le h891 (not_le.mp h1136).le h1135
    · -- right
      by_cases h1137 : z ≤ ((17399/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B041.c837_pos (not_le.mp h1079).le h891 (not_le.mp h1135).le h1137
      · -- right
        exact CKLaneC2R.Cells.S00.B041.c838_pos (not_le.mp h1079).le h891 (not_le.mp h1137).le h1126

theorem strip0_s104 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : z ≤ ((217/400 : ℚ) : ℝ)) (h1079 : ¬ (a ≤ ((59/320 : ℚ) : ℝ))) (h1124 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1125 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h1126 : ¬ (z ≤ ((2289/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1138 : z ≤ ((5491/32000 : ℚ) : ℝ)
  · -- left
    by_cases h1139 : z ≤ ((10069/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1140 : z ≤ ((769/5120 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B043.c871_pos (not_le.mp h1079).le h891 (not_le.mp h1126).le h1140
      · -- right
        exact CKLaneC2R.Cells.S00.B043.c872_pos (not_le.mp h1079).le h891 (not_le.mp h1140).le h1139
    · -- right
      by_cases h1141 : z ≤ ((21051/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B043.c875_pos (not_le.mp h1079).le h891 (not_le.mp h1139).le h1141
      · -- right
        exact CKLaneC2R.Cells.S00.B043.c876_pos (not_le.mp h1079).le h891 (not_le.mp h1141).le h1138
  · -- right
    by_cases h1142 : z ≤ ((2379/12800 : ℚ) : ℝ)
    · -- left
      by_cases h1143 : z ≤ ((22877/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B044.c887_pos (not_le.mp h1079).le h891 (not_le.mp h1138).le h1143
      · -- right
        exact CKLaneC2R.Cells.S00.B044.c888_pos (not_le.mp h1079).le h891 (not_le.mp h1143).le h1142
    · -- right
      by_cases h1144 : z ≤ ((24703/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B044.c891_pos (not_le.mp h1079).le h891 (not_le.mp h1142).le h1144
      · -- right
        exact CKLaneC2R.Cells.S00.B044.c892_pos (not_le.mp h1079).le h891 (not_le.mp h1144).le h1125

end CKLaneC2R.CompactCover


