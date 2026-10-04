-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g51
-- name    : CK_CKLaneC2R_CompactCover_S01_g51
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T08:29:58.849953+00:00
-- url     : https://prove2.me/theorems/a556a79e-a501-4822-83c4-9a215d4f451f
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B052
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B037
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B038

namespace CKLaneC2R.CompactCover

theorem strip1_s068 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : ¬ (a ≤ ((39/160 : ℚ) : ℝ))) (h675 : z ≤ ((217/400 : ℚ) : ℝ)) (h676 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h677 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h678 : a ≤ ((79/320 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h679 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h680 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h681 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h682 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B052.c1040_pos (not_le.mp h598).le h678 hz1 h682
        · -- right
          exact CKLaneC2R.Cells.S01.B052.c1042_pos (not_le.mp h598).le h678 (not_le.mp h682).le h681
      · -- right
        by_cases h683 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B052.c1048_pos (not_le.mp h598).le h678 (not_le.mp h681).le h683
        · -- right
          exact CKLaneC2R.Cells.S01.B052.c1050_pos (not_le.mp h598).le h678 (not_le.mp h683).le h680
    · -- right
      by_cases h684 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B036.c730_pos (not_le.mp h598).le h678 (not_le.mp h680).le h684
      · -- right
        exact CKLaneC2R.Cells.S01.B036.c732_pos (not_le.mp h598).le h678 (not_le.mp h684).le h679
  · -- right
    by_cases h685 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h686 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B037.c754_pos (not_le.mp h598).le h678 (not_le.mp h679).le h686
      · -- right
        exact CKLaneC2R.Cells.S01.B037.c756_pos (not_le.mp h598).le h678 (not_le.mp h686).le h685
    · -- right
      by_cases h687 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B038.c762_pos (not_le.mp h598).le h678 (not_le.mp h685).le h687
      · -- right
        exact CKLaneC2R.Cells.S01.B038.c764_pos (not_le.mp h598).le h678 (not_le.mp h687).le h677

theorem strip1_s069 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : ¬ (a ≤ ((39/160 : ℚ) : ℝ))) (h675 : z ≤ ((217/400 : ℚ) : ℝ)) (h676 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h677 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h678 : ¬ (a ≤ ((79/320 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h688 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h689 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h690 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h691 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B052.c1041_pos (not_le.mp h678).le h0 hz1 h691
        · -- right
          exact CKLaneC2R.Cells.S01.B052.c1043_pos (not_le.mp h678).le h0 (not_le.mp h691).le h690
      · -- right
        by_cases h692 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B052.c1049_pos (not_le.mp h678).le h0 (not_le.mp h690).le h692
        · -- right
          exact CKLaneC2R.Cells.S01.B052.c1051_pos (not_le.mp h678).le h0 (not_le.mp h692).le h689
    · -- right
      by_cases h693 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B036.c731_pos (not_le.mp h678).le h0 (not_le.mp h689).le h693
      · -- right
        exact CKLaneC2R.Cells.S01.B036.c733_pos (not_le.mp h678).le h0 (not_le.mp h693).le h688
  · -- right
    by_cases h694 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h695 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B037.c755_pos (not_le.mp h678).le h0 (not_le.mp h688).le h695
      · -- right
        exact CKLaneC2R.Cells.S01.B037.c757_pos (not_le.mp h678).le h0 (not_le.mp h695).le h694
    · -- right
      by_cases h696 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B038.c763_pos (not_le.mp h678).le h0 (not_le.mp h694).le h696
      · -- right
        exact CKLaneC2R.Cells.S01.B038.c765_pos (not_le.mp h678).le h0 (not_le.mp h696).le h677

end CKLaneC2R.CompactCover


