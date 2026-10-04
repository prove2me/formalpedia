-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g49
-- name    : CK_CKLaneC2R_CompactCover_S00_g49
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T08:06:49.904999+00:00
-- url     : https://prove2.me/theorems/690c984f-5d3b-4d1b-b7b2-7cbf2f6d448f
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B022
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B023

namespace CKLaneC2R.CompactCover

theorem strip0_s059 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : ¬ (a ≤ ((53/320 : ℚ) : ℝ))) (h590 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h645 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h646 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h647 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h648 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        by_cases h649 : z ≤ ((35633/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B018.c379_pos (not_le.mp h482).le h481 (not_le.mp h590).le h649
        · -- right
          exact CKLaneC2R.Cells.S00.B019.c380_pos (not_le.mp h482).le h481 (not_le.mp h649).le h648
      · -- right
        by_cases h650 : z ≤ ((37459/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B019.c383_pos (not_le.mp h482).le h481 (not_le.mp h648).le h650
        · -- right
          exact CKLaneC2R.Cells.S00.B019.c384_pos (not_le.mp h482).le h481 (not_le.mp h650).le h647
    · -- right
      by_cases h651 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        by_cases h652 : z ≤ ((7857/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B019.c395_pos (not_le.mp h482).le h481 (not_le.mp h647).le h652
        · -- right
          exact CKLaneC2R.Cells.S00.B019.c396_pos (not_le.mp h482).le h481 (not_le.mp h652).le h651
      · -- right
        by_cases h653 : z ≤ ((41111/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B019.c399_pos (not_le.mp h482).le h481 (not_le.mp h651).le h653
        · -- right
          exact CKLaneC2R.Cells.S00.B020.c400_pos (not_le.mp h482).le h481 (not_le.mp h653).le h646
  · -- right
    by_cases h654 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h655 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        by_cases h656 : z ≤ ((42937/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B022.c443_pos (not_le.mp h482).le h481 (not_le.mp h646).le h656
        · -- right
          exact CKLaneC2R.Cells.S00.B022.c444_pos (not_le.mp h482).le h481 (not_le.mp h656).le h655
      · -- right
        by_cases h657 : z ≤ ((44763/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B022.c447_pos (not_le.mp h482).le h481 (not_le.mp h655).le h657
        · -- right
          exact CKLaneC2R.Cells.S00.B022.c448_pos (not_le.mp h482).le h481 (not_le.mp h657).le h654
    · -- right
      by_cases h658 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h659 : z ≤ ((46589/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B022.c459_pos (not_le.mp h482).le h481 (not_le.mp h654).le h659
        · -- right
          exact CKLaneC2R.Cells.S00.B023.c460_pos (not_le.mp h482).le h481 (not_le.mp h659).le h658
      · -- right
        by_cases h660 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B023.c463_pos (not_le.mp h482).le h481 (not_le.mp h658).le h660
        · -- right
          exact CKLaneC2R.Cells.S00.B023.c464_pos (not_le.mp h482).le h481 (not_le.mp h660).le h645

end CKLaneC2R.CompactCover


