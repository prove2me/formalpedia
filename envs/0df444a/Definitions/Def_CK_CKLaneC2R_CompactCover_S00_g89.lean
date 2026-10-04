-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g89
-- name    : CK_CKLaneC2R_CompactCover_S00_g89
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T07:55:40.540179+00:00
-- url     : https://prove2.me/theorems/3235545c-f998-4dca-ba0b-3ede5c888d12
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

namespace CKLaneC2R.CompactCover

theorem strip0_s111 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1164 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1185 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1201 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h1211 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1212 : a ≤ ((59/320 : ℚ) : ℝ)
  · -- left
    by_cases h1213 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1214 : z ≤ ((121481/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B051.c1026_pos (not_le.mp h892).le h1212 (not_le.mp h1201).le h1214
      · -- right
        exact CKLaneC2R.Cells.S00.B051.c1028_pos (not_le.mp h892).le h1212 (not_le.mp h1214).le h1213
    · -- right
      by_cases h1215 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B051.c1034_pos (not_le.mp h892).le h1212 (not_le.mp h1213).le h1215
      · -- right
        exact CKLaneC2R.Cells.S00.B051.c1036_pos (not_le.mp h892).le h1212 (not_le.mp h1215).le h1211
  · -- right
    by_cases h1216 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1217 : z ≤ ((121481/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B051.c1027_pos (not_le.mp h1212).le h891 (not_le.mp h1201).le h1217
      · -- right
        exact CKLaneC2R.Cells.S00.B051.c1029_pos (not_le.mp h1212).le h891 (not_le.mp h1217).le h1216
    · -- right
      by_cases h1218 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B051.c1035_pos (not_le.mp h1212).le h891 (not_le.mp h1216).le h1218
      · -- right
        exact CKLaneC2R.Cells.S00.B051.c1037_pos (not_le.mp h1212).le h891 (not_le.mp h1218).le h1211

theorem strip0_s112 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1164 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1185 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1201 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h1211 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h1219 : z ≤ ((63023/64000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1220 : a ≤ ((59/320 : ℚ) : ℝ)
  · -- left
    by_cases h1221 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B052.c1051_pos (not_le.mp h892).le h1220 (not_le.mp h1211).le h1221
    · -- right
      by_cases h1222 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B066.c1337_pos (not_le.mp h892).le h1220 (not_le.mp h1221).le h1222
      · -- right
        exact CKLaneC2R.Cells.S00.B066.c1339_pos (not_le.mp h892).le h1220 (not_le.mp h1222).le h1219
  · -- right
    by_cases h1223 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B052.c1052_pos (not_le.mp h1220).le h891 (not_le.mp h1211).le h1223
    · -- right
      by_cases h1224 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B066.c1338_pos (not_le.mp h1220).le h891 (not_le.mp h1223).le h1224
      · -- right
        exact CKLaneC2R.Cells.S00.B067.c1340_pos (not_le.mp h1220).le h891 (not_le.mp h1224).le h1219

end CKLaneC2R.CompactCover


