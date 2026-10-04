-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g33
-- name    : CK_CKLaneC2R_CompactCover_S01_g33
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T12:26:20.977517+00:00
-- url     : https://prove2.me/theorems/8a7bbadf-8718-4503-a7ee-3a8640beacea
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
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B046
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B054
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B057
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B059

namespace CKLaneC2R.CompactCover

theorem strip1_s041 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : ¬ (a ≤ ((7/32 : ℚ) : ℝ))) (h324 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h376 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h392 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h400 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h406 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h407 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h408 : z ≤ ((121481/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B044.c891_pos (not_le.mp h224).le h1 (not_le.mp h400).le h408
      · -- right
        exact CKLaneC2R.Cells.S01.B044.c892_pos (not_le.mp h224).le h1 (not_le.mp h408).le h407
    · -- right
      by_cases h409 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B044.c895_pos (not_le.mp h224).le h1 (not_le.mp h407).le h409
      · -- right
        exact CKLaneC2R.Cells.S01.B044.c896_pos (not_le.mp h224).le h1 (not_le.mp h409).le h406
  · -- right
    by_cases h410 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h411 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B046.c927_pos (not_le.mp h224).le h1 (not_le.mp h406).le h411
      · -- right
        by_cases h412 : z ≤ ((251179/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B054.c1086_pos (not_le.mp h224).le h1 (not_le.mp h411).le h412
        · -- right
          exact CKLaneC2R.Cells.S01.B054.c1087_pos (not_le.mp h224).le h1 (not_le.mp h412).le h410
    · -- right
      by_cases h413 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h414 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B054.c1097_pos (not_le.mp h224).le h1 (not_le.mp h410).le h414
        · -- right
          exact CKLaneC2R.Cells.S01.B054.c1099_pos (not_le.mp h224).le h1 (not_le.mp h414).le h413
      · -- right
        by_cases h415 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          by_cases h416 : z ≤ ((508749/512000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B057.c1143_pos (not_le.mp h224).le h1 (not_le.mp h413).le h416
          · -- right
            exact CKLaneC2R.Cells.S01.B057.c1144_pos (not_le.mp h224).le h1 (not_le.mp h416).le h415
        · -- right
          by_cases h417 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B057.c1158_pos (not_le.mp h224).le h1 (not_le.mp h415).le h417
          · -- right
            by_cases h418 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B058.c1179_pos (not_le.mp h224).le h1 (not_le.mp h417).le h418
            · -- right
              exact CKLaneC2R.Cells.S01.B059.c1181_pos (not_le.mp h224).le h1 (not_le.mp h418).le hz2

end CKLaneC2R.CompactCover


