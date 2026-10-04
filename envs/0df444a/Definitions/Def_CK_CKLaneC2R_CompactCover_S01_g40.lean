-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g40
-- name    : CK_CKLaneC2R_CompactCover_S01_g40
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T21:59:23.523978+00:00
-- url     : https://prove2.me/theorems/255ac832-b21d-40fb-9856-c5b91a3f27fc
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
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B045
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B046
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B054
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B057
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B059

namespace CKLaneC2R.CompactCover

theorem strip1_s051 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : a ≤ ((37/160 : ℚ) : ℝ)) (h421 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h471 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h487 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h495 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h500 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h501 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h502 : z ≤ ((121481/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B044.c897_pos (not_le.mp h1).le h420 (not_le.mp h495).le h502
      · -- right
        exact CKLaneC2R.Cells.S01.B044.c898_pos (not_le.mp h1).le h420 (not_le.mp h502).le h501
    · -- right
      by_cases h503 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B045.c901_pos (not_le.mp h1).le h420 (not_le.mp h501).le h503
      · -- right
        exact CKLaneC2R.Cells.S01.B045.c902_pos (not_le.mp h1).le h420 (not_le.mp h503).le h500
  · -- right
    by_cases h504 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h505 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B046.c928_pos (not_le.mp h1).le h420 (not_le.mp h500).le h505
      · -- right
        by_cases h506 : z ≤ ((251179/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B054.c1088_pos (not_le.mp h1).le h420 (not_le.mp h505).le h506
        · -- right
          exact CKLaneC2R.Cells.S01.B054.c1089_pos (not_le.mp h1).le h420 (not_le.mp h506).le h504
    · -- right
      by_cases h507 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h508 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B055.c1100_pos (not_le.mp h1).le h420 (not_le.mp h504).le h508
        · -- right
          exact CKLaneC2R.Cells.S01.B055.c1102_pos (not_le.mp h1).le h420 (not_le.mp h508).le h507
      · -- right
        by_cases h509 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          by_cases h510 : z ≤ ((508749/512000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B057.c1145_pos (not_le.mp h1).le h420 (not_le.mp h507).le h510
          · -- right
            exact CKLaneC2R.Cells.S01.B057.c1146_pos (not_le.mp h1).le h420 (not_le.mp h510).le h509
        · -- right
          by_cases h511 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B057.c1159_pos (not_le.mp h1).le h420 (not_le.mp h509).le h511
          · -- right
            by_cases h512 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B059.c1182_pos (not_le.mp h1).le h420 (not_le.mp h511).le h512
            · -- right
              exact CKLaneC2R.Cells.S01.B059.c1184_pos (not_le.mp h1).le h420 (not_le.mp h512).le hz2

end CKLaneC2R.CompactCover


