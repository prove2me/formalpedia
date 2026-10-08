-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g47
-- name    : CK_CKLaneC2R_CompactCover_S01_g47
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T11:39:55.057701+00:00
-- url     : https://prove2.me/theorems/dd8c82a7-1f8b-44cb-bce5-e392fbff7c03
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B010

namespace CKLaneC2R.CompactCover

theorem strip1_s062 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : a ≤ ((39/160 : ℚ) : ℝ)) (h599 : z ≤ ((217/400 : ℚ) : ℝ)) (h600 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h601 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h621 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h622 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h623 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        by_cases h624 : a ≤ ((77/320 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B039.c780_pos (not_le.mp h419).le h624 (not_le.mp h601).le h623
        · -- right
          exact CKLaneC2R.Cells.S01.B039.c781_pos (not_le.mp h624).le h598 (not_le.mp h601).le h623
      · -- right
        exact CKLaneC2R.Cells.S01.B009.c193_pos (not_le.mp h419).le h598 (not_le.mp h623).le h622
    · -- right
      by_cases h625 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B009.c196_pos (not_le.mp h419).le h598 (not_le.mp h622).le h625
      · -- right
        exact CKLaneC2R.Cells.S01.B009.c197_pos (not_le.mp h419).le h598 (not_le.mp h625).le h621
  · -- right
    by_cases h626 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h627 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B010.c200_pos (not_le.mp h419).le h598 (not_le.mp h621).le h627
      · -- right
        exact CKLaneC2R.Cells.S01.B010.c201_pos (not_le.mp h419).le h598 (not_le.mp h627).le h626
    · -- right
      by_cases h628 : a ≤ ((77/320 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B010.c202_pos (not_le.mp h419).le h628 (not_le.mp h626).le h600
      · -- right
        exact CKLaneC2R.Cells.S01.B010.c203_pos (not_le.mp h628).le h598 (not_le.mp h626).le h600

end CKLaneC2R.CompactCover


