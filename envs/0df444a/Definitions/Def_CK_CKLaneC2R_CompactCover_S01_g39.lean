-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g39
-- name    : CK_CKLaneC2R_CompactCover_S01_g39
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T17:45:35.080269+00:00
-- url     : https://prove2.me/theorems/c5dfe524-34d9-4fc8-9c35-24fb71a9604b
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B044

namespace CKLaneC2R.CompactCover

theorem strip1_s050 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : a ≤ ((37/160 : ℚ) : ℝ)) (h421 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h471 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h487 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h495 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h496 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h497 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B028.c576_pos (not_le.mp h1).le h420 (not_le.mp h487).le h497
    · -- right
      exact CKLaneC2R.Cells.S01.B028.c577_pos (not_le.mp h1).le h420 (not_le.mp h497).le h496
  · -- right
    by_cases h498 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B029.c584_pos (not_le.mp h1).le h420 (not_le.mp h496).le h498
    · -- right
      by_cases h499 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B044.c880_pos (not_le.mp h1).le h420 (not_le.mp h498).le h499
      · -- right
        exact CKLaneC2R.Cells.S01.B044.c881_pos (not_le.mp h1).le h420 (not_le.mp h499).le h495

end CKLaneC2R.CompactCover


