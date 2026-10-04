-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g74
-- name    : CK_CKLaneC2R_CompactCover_S00_g74
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T10:35:44.880621+00:00
-- url     : https://prove2.me/theorems/c33404b2-6722-48bc-a6cc-96efdc79ab13
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B066
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B067
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B071
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B072
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B074
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B075

namespace CKLaneC2R.CompactCover

theorem strip0_s090 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : a ≤ ((57/320 : ℚ) : ℝ)) (h894 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h943 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h959 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h967 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h973 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h977 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h978 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      by_cases h979 : z ≤ ((249353/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B066.c1331_pos (not_le.mp h0).le h893 (not_le.mp h973).le h979
      · -- right
        exact CKLaneC2R.Cells.S00.B066.c1332_pos (not_le.mp h0).le h893 (not_le.mp h979).le h978
    · -- right
      by_cases h980 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B066.c1333_pos (not_le.mp h0).le h893 (not_le.mp h978).le h980
      · -- right
        exact CKLaneC2R.Cells.S00.B066.c1335_pos (not_le.mp h0).le h893 (not_le.mp h980).le h977
  · -- right
    by_cases h981 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h982 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B067.c1351_pos (not_le.mp h0).le h893 (not_le.mp h977).le h982
      · -- right
        exact CKLaneC2R.Cells.S00.B067.c1353_pos (not_le.mp h0).le h893 (not_le.mp h982).le h981
    · -- right
      by_cases h983 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h984 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B071.c1436_pos (not_le.mp h0).le h893 (not_le.mp h981).le h984
        · -- right
          exact CKLaneC2R.Cells.S00.B071.c1438_pos (not_le.mp h0).le h893 (not_le.mp h984).le h983
      · -- right
        by_cases h985 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B072.c1446_pos (not_le.mp h0).le h893 (not_le.mp h983).le h985
        · -- right
          by_cases h986 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B074.c1480_pos (not_le.mp h0).le h893 (not_le.mp h985).le h986
          · -- right
            by_cases h987 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S00.B075.c1506_pos (not_le.mp h0).le h893 (not_le.mp h986).le h987
            · -- right
              exact CKLaneC2R.Cells.S00.B075.c1508_pos (not_le.mp h0).le h893 (not_le.mp h987).le hz2

end CKLaneC2R.CompactCover


