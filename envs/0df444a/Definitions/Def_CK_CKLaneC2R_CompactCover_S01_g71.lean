-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g71
-- name    : CK_CKLaneC2R_CompactCover_S01_g71
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T16:55:11.993849+00:00
-- url     : https://prove2.me/theorems/5c6d0a6c-bb7a-4e0b-8e76-5bc5fa181f64
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B046
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B047
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B056
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B059

namespace CKLaneC2R.CompactCover

theorem strip1_s102 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : ¬ (a ≤ ((21/80 : ℚ) : ℝ))) (h880 : ¬ (a ≤ ((43/160 : ℚ) : ℝ))) (h941 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h971 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h979 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h984 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h985 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h986 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B029.c597_pos (not_le.mp h880).le h746 (not_le.mp h979).le h986
      · -- right
        exact CKLaneC2R.Cells.S01.B029.c598_pos (not_le.mp h880).le h746 (not_le.mp h986).le h985
    · -- right
      by_cases h987 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B030.c604_pos (not_le.mp h880).le h746 (not_le.mp h985).le h987
      · -- right
        exact CKLaneC2R.Cells.S01.B030.c606_pos (not_le.mp h880).le h746 (not_le.mp h987).le h984
  · -- right
    by_cases h988 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h989 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B031.c625_pos (not_le.mp h880).le h746 (not_le.mp h984).le h989
      · -- right
        by_cases h990 : z ≤ ((123307/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B046.c921_pos (not_le.mp h880).le h746 (not_le.mp h989).le h990
        · -- right
          exact CKLaneC2R.Cells.S01.B046.c922_pos (not_le.mp h880).le h746 (not_le.mp h990).le h988
    · -- right
      by_cases h991 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h992 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B046.c938_pos (not_le.mp h880).le h746 (not_le.mp h988).le h992
        · -- right
          exact CKLaneC2R.Cells.S01.B047.c940_pos (not_le.mp h880).le h746 (not_le.mp h992).le h991
      · -- right
        by_cases h993 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h994 : z ≤ ((50601/51200 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B055.c1113_pos (not_le.mp h880).le h746 (not_le.mp h991).le h994
          · -- right
            exact CKLaneC2R.Cells.S01.B055.c1115_pos (not_le.mp h880).le h746 (not_le.mp h994).le h993
        · -- right
          by_cases h995 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B056.c1123_pos (not_le.mp h880).le h746 (not_le.mp h993).le h995
          · -- right
            by_cases h996 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B058.c1166_pos (not_le.mp h880).le h746 (not_le.mp h995).le h996
            · -- right
              by_cases h997 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S01.B059.c1195_pos (not_le.mp h880).le h746 (not_le.mp h996).le h997
              · -- right
                exact CKLaneC2R.Cells.S01.B059.c1197_pos (not_le.mp h880).le h746 (not_le.mp h997).le hz2

end CKLaneC2R.CompactCover


