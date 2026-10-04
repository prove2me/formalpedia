-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g62
-- name    : CK_CKLaneC2R_CompactCover_S00_g62
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T17:09:21.4663+00:00
-- url     : https://prove2.me/theorems/1f4731b9-bdb2-437f-92d8-96c6372fb92f
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B003
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B004

namespace CKLaneC2R.CompactCover

theorem strip0_s075 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : ¬ (a ≤ ((11/64 : ℚ) : ℝ))) (h794 : z ≤ ((217/400 : ℚ) : ℝ)) (h795 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h796 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h820 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h821 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h822 : a ≤ ((111/640 : ℚ) : ℝ)
      · -- left
        by_cases h823 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B039.c793_pos (not_le.mp h693).le h822 (not_le.mp h796).le h823
        · -- right
          exact CKLaneC2R.Cells.S00.B039.c795_pos (not_le.mp h693).le h822 (not_le.mp h823).le h821
      · -- right
        by_cases h824 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B039.c794_pos (not_le.mp h822).le h0 (not_le.mp h796).le h824
        · -- right
          exact CKLaneC2R.Cells.S00.B039.c796_pos (not_le.mp h822).le h0 (not_le.mp h824).le h821
    · -- right
      by_cases h825 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        by_cases h826 : a ≤ ((111/640 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B040.c801_pos (not_le.mp h693).le h826 (not_le.mp h821).le h825
        · -- right
          exact CKLaneC2R.Cells.S00.B040.c802_pos (not_le.mp h826).le h0 (not_le.mp h821).le h825
      · -- right
        exact CKLaneC2R.Cells.S00.B003.c67_pos (not_le.mp h693).le h0 (not_le.mp h825).le h820
  · -- right
    by_cases h827 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h828 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B003.c75_pos (not_le.mp h693).le h0 (not_le.mp h820).le h828
      · -- right
        exact CKLaneC2R.Cells.S00.B003.c76_pos (not_le.mp h693).le h0 (not_le.mp h828).le h827
    · -- right
      by_cases h829 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B003.c79_pos (not_le.mp h693).le h0 (not_le.mp h827).le h829
      · -- right
        exact CKLaneC2R.Cells.S00.B004.c80_pos (not_le.mp h693).le h0 (not_le.mp h829).le h795

end CKLaneC2R.CompactCover


