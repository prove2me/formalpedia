-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g41
-- name    : CK_CKLaneC2R_CompactCover_S00_g41
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T03:39:45.096293+00:00
-- url     : https://prove2.me/theorems/4eb7d529-1534-45e2-9f47-934f4b1e99c2
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

theorem strip0_s048 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : a ≤ ((53/320 : ℚ) : ℝ)) (h483 : z ≤ ((217/400 : ℚ) : ℝ)) (h484 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h485 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h514 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h515 : a ≤ ((21/128 : ℚ) : ℝ)
    · -- left
      by_cases h516 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        by_cases h517 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B038.c773_pos (not_le.mp h1).le h515 (not_le.mp h485).le h517
        · -- right
          exact CKLaneC2R.Cells.S00.B038.c775_pos (not_le.mp h1).le h515 (not_le.mp h517).le h516
      · -- right
        by_cases h518 : z ≤ ((15547/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B039.c781_pos (not_le.mp h1).le h515 (not_le.mp h516).le h518
        · -- right
          exact CKLaneC2R.Cells.S00.B039.c783_pos (not_le.mp h1).le h515 (not_le.mp h518).le h514
    · -- right
      by_cases h519 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        by_cases h520 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B038.c774_pos (not_le.mp h515).le h482 (not_le.mp h485).le h520
        · -- right
          exact CKLaneC2R.Cells.S00.B038.c776_pos (not_le.mp h515).le h482 (not_le.mp h520).le h519
      · -- right
        by_cases h521 : z ≤ ((15547/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B039.c782_pos (not_le.mp h515).le h482 (not_le.mp h519).le h521
        · -- right
          exact CKLaneC2R.Cells.S00.B039.c784_pos (not_le.mp h515).le h482 (not_le.mp h521).le h514
  · -- right
    by_cases h522 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h523 : a ≤ ((21/128 : ℚ) : ℝ)
      · -- left
        by_cases h524 : z ≤ ((17373/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B040.c803_pos (not_le.mp h1).le h523 (not_le.mp h514).le h524
        · -- right
          exact CKLaneC2R.Cells.S00.B040.c805_pos (not_le.mp h1).le h523 (not_le.mp h524).le h522
      · -- right
        by_cases h525 : z ≤ ((17373/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B040.c804_pos (not_le.mp h523).le h482 (not_le.mp h514).le h525
        · -- right
          exact CKLaneC2R.Cells.S00.B040.c806_pos (not_le.mp h523).le h482 (not_le.mp h525).le h522
    · -- right
      by_cases h526 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B003.c69_pos (not_le.mp h1).le h482 (not_le.mp h522).le h526
      · -- right
        exact CKLaneC2R.Cells.S00.B003.c70_pos (not_le.mp h1).le h482 (not_le.mp h526).le h484

end CKLaneC2R.CompactCover


