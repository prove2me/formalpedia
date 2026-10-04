-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g24
-- name    : CK_CKLaneC2R_CompactCover_S01_g24
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T09:42:01.612885+00:00
-- url     : https://prove2.me/theorems/d3b95ff5-eb9f-4ae9-ae7f-a102d8e6f976
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B044
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B054
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B057
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B059

namespace CKLaneC2R.CompactCover

theorem strip1_s031 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : a ≤ ((7/32 : ℚ) : ℝ)) (h225 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h280 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h296 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h304 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h310 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h311 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h312 : z ≤ ((121481/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B044.c889_pos (not_le.mp h2).le h224 (not_le.mp h304).le h312
      · -- right
        exact CKLaneC2R.Cells.S01.B044.c890_pos (not_le.mp h2).le h224 (not_le.mp h312).le h311
    · -- right
      by_cases h313 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B044.c893_pos (not_le.mp h2).le h224 (not_le.mp h311).le h313
      · -- right
        exact CKLaneC2R.Cells.S01.B044.c894_pos (not_le.mp h2).le h224 (not_le.mp h313).le h310
  · -- right
    by_cases h314 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h315 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        by_cases h316 : z ≤ ((249353/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B054.c1082_pos (not_le.mp h2).le h224 (not_le.mp h310).le h316
        · -- right
          exact CKLaneC2R.Cells.S01.B054.c1083_pos (not_le.mp h2).le h224 (not_le.mp h316).le h315
      · -- right
        by_cases h317 : z ≤ ((251179/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B054.c1084_pos (not_le.mp h2).le h224 (not_le.mp h315).le h317
        · -- right
          exact CKLaneC2R.Cells.S01.B054.c1085_pos (not_le.mp h2).le h224 (not_le.mp h317).le h314
    · -- right
      by_cases h318 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h319 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B054.c1096_pos (not_le.mp h2).le h224 (not_le.mp h314).le h319
        · -- right
          exact CKLaneC2R.Cells.S01.B054.c1098_pos (not_le.mp h2).le h224 (not_le.mp h319).le h318
      · -- right
        by_cases h320 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          by_cases h321 : z ≤ ((508749/512000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B057.c1141_pos (not_le.mp h2).le h224 (not_le.mp h318).le h321
          · -- right
            exact CKLaneC2R.Cells.S01.B057.c1142_pos (not_le.mp h2).le h224 (not_le.mp h321).le h320
        · -- right
          by_cases h322 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B057.c1157_pos (not_le.mp h2).le h224 (not_le.mp h320).le h322
          · -- right
            by_cases h323 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B058.c1178_pos (not_le.mp h2).le h224 (not_le.mp h322).le h323
            · -- right
              exact CKLaneC2R.Cells.S01.B059.c1180_pos (not_le.mp h2).le h224 (not_le.mp h323).le hz2

end CKLaneC2R.CompactCover


