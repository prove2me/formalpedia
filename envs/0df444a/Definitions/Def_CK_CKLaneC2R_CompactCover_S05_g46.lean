-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g46
-- name    : CK_CKLaneC2R_CompactCover_S05_g46
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T11:24:26.3923+00:00
-- url     : https://prove2.me/theorems/2f3e9ab5-a3c2-4ee4-bd46-6b736ceb3628
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B034

namespace CKLaneC2R.CompactCover

theorem strip5_s084 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : a ≤ ((31869/32000 : ℚ) : ℝ)) (h474 : ¬ (a ≤ ((63639/64000 : ℚ) : ℝ))) (h507 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h516 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h520 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h523 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h526 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h530 : ¬ (z ≤ ((63023/64000 : ℚ) : ℝ))) (h535 : ¬ (a ≤ ((127377/128000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h542 : z ≤ ((126959/128000 : ℚ) : ℝ)
  · -- left
    by_cases h543 : z ≤ ((50601/51200 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B030.c615_pos (not_le.mp h535).le h473 (not_le.mp h530).le h543
    · -- right
      exact CKLaneC2R.Cells.S05.B030.c619_pos (not_le.mp h535).le h473 (not_le.mp h543).le h542
  · -- right
    by_cases h544 : z ≤ ((254831/256000 : ℚ) : ℝ)
    · -- left
      by_cases h545 : z ≤ ((508749/512000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B032.c656_pos (not_le.mp h535).le h473 (not_le.mp h542).le h545
      · -- right
        exact CKLaneC2R.Cells.S05.B032.c658_pos (not_le.mp h535).le h473 (not_le.mp h545).le h544
    · -- right
      by_cases h546 : z ≤ ((20423/20480 : ℚ) : ℝ)
      · -- left
        by_cases h547 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B033.c671_pos (not_le.mp h535).le h473 (not_le.mp h544).le h547
        · -- right
          exact CKLaneC2R.Cells.S05.B033.c672_pos (not_le.mp h535).le h473 (not_le.mp h547).le h546
      · -- right
        by_cases h548 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B033.c675_pos (not_le.mp h535).le h473 (not_le.mp h546).le h548
        · -- right
          by_cases h549 : a ≤ ((254853/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B034.c688_pos (not_le.mp h535).le h549 (not_le.mp h548).le hz2
          · -- right
            exact CKLaneC2R.Cells.S05.B034.c689_pos (not_le.mp h549).le h473 (not_le.mp h548).le hz2

end CKLaneC2R.CompactCover


