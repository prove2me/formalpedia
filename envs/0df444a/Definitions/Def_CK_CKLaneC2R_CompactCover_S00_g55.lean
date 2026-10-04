-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g55
-- name    : CK_CKLaneC2R_CompactCover_S00_g55
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T22:50:55.192686+00:00
-- url     : https://prove2.me/theorems/e2c6c965-dbcb-4ad7-b011-ec7390d18647
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

namespace CKLaneC2R.CompactCover

theorem strip0_s066 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : a ≤ ((11/64 : ℚ) : ℝ)) (h694 : z ≤ ((217/400 : ℚ) : ℝ)) (h695 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h696 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h721 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h722 : a ≤ ((109/640 : ℚ) : ℝ)
    · -- left
      by_cases h723 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        by_cases h724 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B039.c789_pos (not_le.mp h481).le h722 (not_le.mp h696).le h724
        · -- right
          exact CKLaneC2R.Cells.S00.B039.c791_pos (not_le.mp h481).le h722 (not_le.mp h724).le h723
      · -- right
        by_cases h725 : z ≤ ((15547/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B039.c797_pos (not_le.mp h481).le h722 (not_le.mp h723).le h725
        · -- right
          exact CKLaneC2R.Cells.S00.B039.c799_pos (not_le.mp h481).le h722 (not_le.mp h725).le h721
    · -- right
      by_cases h726 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        by_cases h727 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B039.c790_pos (not_le.mp h722).le h693 (not_le.mp h696).le h727
        · -- right
          exact CKLaneC2R.Cells.S00.B039.c792_pos (not_le.mp h722).le h693 (not_le.mp h727).le h726
      · -- right
        by_cases h728 : z ≤ ((15547/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B039.c798_pos (not_le.mp h722).le h693 (not_le.mp h726).le h728
        · -- right
          exact CKLaneC2R.Cells.S00.B040.c800_pos (not_le.mp h722).le h693 (not_le.mp h728).le h721
  · -- right
    by_cases h729 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h730 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B003.c73_pos (not_le.mp h481).le h693 (not_le.mp h721).le h730
      · -- right
        exact CKLaneC2R.Cells.S00.B003.c74_pos (not_le.mp h481).le h693 (not_le.mp h730).le h729
    · -- right
      by_cases h731 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B003.c77_pos (not_le.mp h481).le h693 (not_le.mp h729).le h731
      · -- right
        exact CKLaneC2R.Cells.S00.B003.c78_pos (not_le.mp h481).le h693 (not_le.mp h731).le h695

end CKLaneC2R.CompactCover


