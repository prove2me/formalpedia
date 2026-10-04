-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g58
-- name    : CK_CKLaneC2R_CompactCover_S05_g58
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T16:27:08.840574+00:00
-- url     : https://prove2.me/theorems/2f4eb689-4457-4ecd-bf0d-c64e8257ef36
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
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B035

namespace CKLaneC2R.CompactCover

theorem strip5_s109 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : a ≤ ((127773/128000 : ℚ) : ℝ)) (h617 : ¬ (a ≤ ((255447/256000 : ℚ) : ℝ))) (h642 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h647 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h649 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h651 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h653 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h655 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h656 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B030.c600_pos (not_le.mp h617).le h616 (not_le.mp h653).le h656
    · -- right
      by_cases h657 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B031.c623_pos (not_le.mp h617).le h616 (not_le.mp h656).le h657
      · -- right
        exact CKLaneC2R.Cells.S05.B031.c625_pos (not_le.mp h617).le h616 (not_le.mp h657).le h655
  · -- right
    by_cases h658 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h659 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B032.c645_pos (not_le.mp h617).le h616 (not_le.mp h655).le h659
      · -- right
        exact CKLaneC2R.Cells.S05.B032.c649_pos (not_le.mp h617).le h616 (not_le.mp h659).le h658
    · -- right
      by_cases h660 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h661 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B033.c679_pos (not_le.mp h617).le h616 (not_le.mp h658).le h661
        · -- right
          exact CKLaneC2R.Cells.S05.B034.c681_pos (not_le.mp h617).le h616 (not_le.mp h661).le h660
      · -- right
        by_cases h662 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          by_cases h663 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B035.c702_pos (not_le.mp h617).le h616 (not_le.mp h660).le h663
          · -- right
            exact CKLaneC2R.Cells.S05.B035.c704_pos (not_le.mp h617).le h616 (not_le.mp h663).le h662
        · -- right
          by_cases h664 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            by_cases h665 : z ≤ ((2043213/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B035.c714_pos (not_le.mp h617).le h616 (not_le.mp h662).le h665
            · -- right
              exact CKLaneC2R.Cells.S05.B035.c715_pos (not_le.mp h617).le h616 (not_le.mp h665).le h664
          · -- right
            by_cases h666 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B035.c718_pos (not_le.mp h617).le h616 (not_le.mp h664).le h666
            · -- right
              exact CKLaneC2R.Cells.S05.B035.c719_pos (not_le.mp h617).le h616 (not_le.mp h666).le hz2

end CKLaneC2R.CompactCover


