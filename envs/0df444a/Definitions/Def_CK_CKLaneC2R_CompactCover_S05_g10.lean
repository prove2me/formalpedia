-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g10
-- name    : CK_CKLaneC2R_CompactCover_S05_g10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T14:08:24.379322+00:00
-- url     : https://prove2.me/theorems/1cfd91d1-38c8-4822-8fc8-1165fe8dc237
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S05 (proof part of strip5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S05 (proof part of strip5).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B023

namespace CKLaneC2R.CompactCover

theorem strip5_s016 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((3699/4000 : ℚ) : ℝ))) (h69 : ¬ (a ≤ ((7497/8000 : ℚ) : ℝ))) (h107 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h116 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h121 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h126 : a ≤ ((15093/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h127 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h128 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B009.c197_pos (not_le.mp h69).le h126 (not_le.mp h121).le h128
    · -- right
      by_cases h129 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B012.c249_pos (not_le.mp h69).le h126 (not_le.mp h128).le h129
      · -- right
        exact CKLaneC2R.Cells.S05.B012.c251_pos (not_le.mp h69).le h126 (not_le.mp h129).le h127
  · -- right
    by_cases h130 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h131 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B013.c263_pos (not_le.mp h69).le h126 (not_le.mp h127).le h131
      · -- right
        exact CKLaneC2R.Cells.S05.B013.c265_pos (not_le.mp h69).le h126 (not_le.mp h131).le h130
    · -- right
      by_cases h132 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h133 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B016.c330_pos (not_le.mp h69).le h126 (not_le.mp h130).le h133
        · -- right
          exact CKLaneC2R.Cells.S05.B016.c331_pos (not_le.mp h69).le h126 (not_le.mp h133).le h132
      · -- right
        by_cases h134 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B017.c341_pos (not_le.mp h69).le h126 (not_le.mp h132).le h134
        · -- right
          by_cases h135 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B020.c407_pos (not_le.mp h69).le h126 (not_le.mp h134).le h135
          · -- right
            by_cases h136 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B023.c473_pos (not_le.mp h69).le h126 (not_le.mp h135).le h136
            · -- right
              exact CKLaneC2R.Cells.S05.B023.c474_pos (not_le.mp h69).le h126 (not_le.mp h136).le hz2

end CKLaneC2R.CompactCover


