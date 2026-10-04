-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g57
-- name    : CK_CKLaneC2R_CompactCover_S00_g57
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T08:56:54.316101+00:00
-- url     : https://prove2.me/theorems/5e7a88a8-dd96-488a-91a8-efcf08d20752
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B022
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B023

namespace CKLaneC2R.CompactCover

theorem strip0_s068 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : a ≤ ((11/64 : ℚ) : ℝ)) (h694 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h747 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h748 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h749 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h750 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        by_cases h751 : z ≤ ((35633/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B019.c385_pos (not_le.mp h481).le h693 (not_le.mp h694).le h751
        · -- right
          exact CKLaneC2R.Cells.S00.B019.c386_pos (not_le.mp h481).le h693 (not_le.mp h751).le h750
      · -- right
        by_cases h752 : z ≤ ((37459/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B019.c389_pos (not_le.mp h481).le h693 (not_le.mp h750).le h752
        · -- right
          exact CKLaneC2R.Cells.S00.B019.c390_pos (not_le.mp h481).le h693 (not_le.mp h752).le h749
    · -- right
      by_cases h753 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        by_cases h754 : z ≤ ((7857/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B020.c401_pos (not_le.mp h481).le h693 (not_le.mp h749).le h754
        · -- right
          exact CKLaneC2R.Cells.S00.B020.c402_pos (not_le.mp h481).le h693 (not_le.mp h754).le h753
      · -- right
        by_cases h755 : z ≤ ((41111/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B020.c405_pos (not_le.mp h481).le h693 (not_le.mp h753).le h755
        · -- right
          exact CKLaneC2R.Cells.S00.B020.c406_pos (not_le.mp h481).le h693 (not_le.mp h755).le h748
  · -- right
    by_cases h756 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h757 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        by_cases h758 : z ≤ ((42937/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B022.c449_pos (not_le.mp h481).le h693 (not_le.mp h748).le h758
        · -- right
          exact CKLaneC2R.Cells.S00.B022.c450_pos (not_le.mp h481).le h693 (not_le.mp h758).le h757
      · -- right
        by_cases h759 : z ≤ ((44763/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B022.c453_pos (not_le.mp h481).le h693 (not_le.mp h757).le h759
        · -- right
          exact CKLaneC2R.Cells.S00.B022.c454_pos (not_le.mp h481).le h693 (not_le.mp h759).le h756
    · -- right
      by_cases h760 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h761 : z ≤ ((46589/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B023.c465_pos (not_le.mp h481).le h693 (not_le.mp h756).le h761
        · -- right
          exact CKLaneC2R.Cells.S00.B023.c466_pos (not_le.mp h481).le h693 (not_le.mp h761).le h760
      · -- right
        by_cases h762 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B023.c469_pos (not_le.mp h481).le h693 (not_le.mp h760).le h762
        · -- right
          exact CKLaneC2R.Cells.S00.B023.c470_pos (not_le.mp h481).le h693 (not_le.mp h762).le h747

end CKLaneC2R.CompactCover


