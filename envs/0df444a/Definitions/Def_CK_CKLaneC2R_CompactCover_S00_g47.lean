-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g47
-- name    : CK_CKLaneC2R_CompactCover_S00_g47
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T13:50:41.163207+00:00
-- url     : https://prove2.me/theorems/725f3116-2985-41db-bb94-56342f9cdf29
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B038
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B003

namespace CKLaneC2R.CompactCover

theorem strip0_s057 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : ¬ (a ≤ ((53/320 : ℚ) : ℝ))) (h590 : z ≤ ((217/400 : ℚ) : ℝ)) (h591 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h592 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h618 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h619 : a ≤ ((107/640 : ℚ) : ℝ)
    · -- left
      by_cases h620 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        by_cases h621 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B038.c777_pos (not_le.mp h482).le h619 (not_le.mp h592).le h621
        · -- right
          exact CKLaneC2R.Cells.S00.B038.c779_pos (not_le.mp h482).le h619 (not_le.mp h621).le h620
      · -- right
        by_cases h622 : z ≤ ((15547/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B039.c785_pos (not_le.mp h482).le h619 (not_le.mp h620).le h622
        · -- right
          exact CKLaneC2R.Cells.S00.B039.c787_pos (not_le.mp h482).le h619 (not_le.mp h622).le h618
    · -- right
      by_cases h623 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        by_cases h624 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B038.c778_pos (not_le.mp h619).le h481 (not_le.mp h592).le h624
        · -- right
          exact CKLaneC2R.Cells.S00.B039.c780_pos (not_le.mp h619).le h481 (not_le.mp h624).le h623
      · -- right
        by_cases h625 : z ≤ ((15547/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B039.c786_pos (not_le.mp h619).le h481 (not_le.mp h623).le h625
        · -- right
          exact CKLaneC2R.Cells.S00.B039.c788_pos (not_le.mp h619).le h481 (not_le.mp h625).le h618
  · -- right
    by_cases h626 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h627 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        by_cases h628 : a ≤ ((107/640 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B040.c807_pos (not_le.mp h482).le h628 (not_le.mp h618).le h627
        · -- right
          exact CKLaneC2R.Cells.S00.B040.c808_pos (not_le.mp h628).le h481 (not_le.mp h618).le h627
      · -- right
        exact CKLaneC2R.Cells.S00.B003.c68_pos (not_le.mp h482).le h481 (not_le.mp h627).le h626
    · -- right
      by_cases h629 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B003.c71_pos (not_le.mp h482).le h481 (not_le.mp h626).le h629
      · -- right
        exact CKLaneC2R.Cells.S00.B003.c72_pos (not_le.mp h482).le h481 (not_le.mp h629).le h591

end CKLaneC2R.CompactCover


