-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g75
-- name    : CK_CKLaneC2R_CompactCover_S00_g75
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T03:05:22.579188+00:00
-- url     : https://prove2.me/theorems/9b465fa2-a972-4606-9db8-e5f917cea556
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B061
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B062
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B063
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B041

namespace CKLaneC2R.CompactCover

theorem strip0_s091 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : ¬ (a ≤ ((57/320 : ℚ) : ℝ))) (h988 : z ≤ ((217/400 : ℚ) : ℝ)) (h989 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h990 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h991 : z ≤ ((2289/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h992 : z ≤ ((733/6400 : ℚ) : ℝ)
  · -- left
    by_cases h993 : a ≤ ((23/128 : ℚ) : ℝ)
    · -- left
      by_cases h994 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h995 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B061.c1229_pos (not_le.mp h893).le h993 hz1 h995
        · -- right
          exact CKLaneC2R.Cells.S00.B061.c1231_pos (not_le.mp h893).le h993 (not_le.mp h995).le h994
      · -- right
        by_cases h996 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B061.c1237_pos (not_le.mp h893).le h993 (not_le.mp h994).le h996
        · -- right
          exact CKLaneC2R.Cells.S00.B061.c1239_pos (not_le.mp h893).le h993 (not_le.mp h996).le h992
    · -- right
      by_cases h997 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h998 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B061.c1230_pos (not_le.mp h993).le h892 hz1 h998
        · -- right
          exact CKLaneC2R.Cells.S00.B061.c1232_pos (not_le.mp h993).le h892 (not_le.mp h998).le h997
      · -- right
        by_cases h999 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B061.c1238_pos (not_le.mp h993).le h892 (not_le.mp h997).le h999
        · -- right
          exact CKLaneC2R.Cells.S00.B062.c1240_pos (not_le.mp h993).le h892 (not_le.mp h999).le h992
  · -- right
    by_cases h1000 : z ≤ ((8243/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1001 : a ≤ ((23/128 : ℚ) : ℝ)
      · -- left
        by_cases h1002 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B063.c1261_pos (not_le.mp h893).le h1001 (not_le.mp h992).le h1002
        · -- right
          exact CKLaneC2R.Cells.S00.B063.c1263_pos (not_le.mp h893).le h1001 (not_le.mp h1002).le h1000
      · -- right
        by_cases h1003 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B063.c1262_pos (not_le.mp h1001).le h892 (not_le.mp h992).le h1003
        · -- right
          exact CKLaneC2R.Cells.S00.B063.c1264_pos (not_le.mp h1001).le h892 (not_le.mp h1003).le h1000
    · -- right
      by_cases h1004 : z ≤ ((17399/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B041.c830_pos (not_le.mp h893).le h892 (not_le.mp h1000).le h1004
      · -- right
        exact CKLaneC2R.Cells.S00.B041.c831_pos (not_le.mp h893).le h892 (not_le.mp h1004).le h991

end CKLaneC2R.CompactCover


