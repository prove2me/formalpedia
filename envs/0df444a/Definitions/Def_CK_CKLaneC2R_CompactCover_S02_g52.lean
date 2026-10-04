-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g52
-- name    : CK_CKLaneC2R_CompactCover_S02_g52
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T21:32:13.002735+00:00
-- url     : https://prove2.me/theorems/5566841c-9a5c-47f0-ac2a-af998545b9ed
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S02 (proof part of strip2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S02 (proof part of strip2).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B022
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B001

namespace CKLaneC2R.CompactCover

theorem strip2_s076 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) (h717 : ¬ (a ≤ ((19/40 : ℚ) : ℝ))) (h792 : z ≤ ((217/400 : ℚ) : ℝ)) (h793 : a ≤ ((39/80 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h794 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h795 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h796 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h797 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h798 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B022.c443_pos (not_le.mp h717).le h793 hz1 h798
          · -- right
            exact CKLaneC2R.Cells.S02.B022.c444_pos (not_le.mp h717).le h793 (not_le.mp h798).le h797
        · -- right
          by_cases h799 : z ≤ ((8243/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B022.c447_pos (not_le.mp h717).le h793 (not_le.mp h797).le h799
          · -- right
            exact CKLaneC2R.Cells.S02.B022.c448_pos (not_le.mp h717).le h793 (not_le.mp h799).le h796
      · -- right
        by_cases h800 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          by_cases h801 : z ≤ ((10069/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B022.c455_pos (not_le.mp h717).le h793 (not_le.mp h796).le h801
          · -- right
            exact CKLaneC2R.Cells.S02.B022.c456_pos (not_le.mp h717).le h793 (not_le.mp h801).le h800
        · -- right
          exact CKLaneC2R.Cells.S02.B004.c82_pos (not_le.mp h717).le h793 (not_le.mp h800).le h795
    · -- right
      by_cases h802 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        by_cases h803 : z ≤ ((7317/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B004.c92_pos (not_le.mp h717).le h793 (not_le.mp h795).le h803
        · -- right
          exact CKLaneC2R.Cells.S02.B004.c94_pos (not_le.mp h717).le h793 (not_le.mp h803).le h802
      · -- right
        by_cases h804 : z ≤ ((9143/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B004.c96_pos (not_le.mp h717).le h793 (not_le.mp h802).le h804
        · -- right
          exact CKLaneC2R.Cells.S02.B004.c97_pos (not_le.mp h717).le h793 (not_le.mp h804).le h794
  · -- right
    by_cases h805 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h806 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        by_cases h807 : z ≤ ((10969/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B007.c140_pos (not_le.mp h717).le h793 (not_le.mp h794).le h807
        · -- right
          exact CKLaneC2R.Cells.S02.B007.c141_pos (not_le.mp h717).le h793 (not_le.mp h807).le h806
      · -- right
        exact CKLaneC2R.Cells.S02.B000.c0_pos (not_le.mp h717).le h793 (not_le.mp h806).le h805
    · -- right
      by_cases h808 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B000.c5_pos (not_le.mp h717).le h793 (not_le.mp h805).le h808
      · -- right
        exact CKLaneC2R.Cells.S02.B000.c7_pos (not_le.mp h717).le h793 (not_le.mp h808).le h792

theorem strip2_s077 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) (h717 : ¬ (a ≤ ((19/40 : ℚ) : ℝ))) (h792 : z ≤ ((217/400 : ℚ) : ℝ)) (h793 : ¬ (a ≤ ((39/80 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h809 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h810 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h811 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h812 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h813 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B022.c445_pos (not_le.mp h793).le ha2 hz1 h813
          · -- right
            exact CKLaneC2R.Cells.S02.B022.c446_pos (not_le.mp h793).le ha2 (not_le.mp h813).le h812
        · -- right
          by_cases h814 : z ≤ ((8243/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B022.c449_pos (not_le.mp h793).le ha2 (not_le.mp h812).le h814
          · -- right
            exact CKLaneC2R.Cells.S02.B022.c450_pos (not_le.mp h793).le ha2 (not_le.mp h814).le h811
      · -- right
        by_cases h815 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B004.c81_pos (not_le.mp h793).le ha2 (not_le.mp h811).le h815
        · -- right
          exact CKLaneC2R.Cells.S02.B004.c83_pos (not_le.mp h793).le ha2 (not_le.mp h815).le h810
    · -- right
      by_cases h816 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        by_cases h817 : z ≤ ((7317/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B004.c93_pos (not_le.mp h793).le ha2 (not_le.mp h810).le h817
        · -- right
          exact CKLaneC2R.Cells.S02.B004.c95_pos (not_le.mp h793).le ha2 (not_le.mp h817).le h816
      · -- right
        by_cases h818 : z ≤ ((9143/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B004.c98_pos (not_le.mp h793).le ha2 (not_le.mp h816).le h818
        · -- right
          exact CKLaneC2R.Cells.S02.B004.c99_pos (not_le.mp h793).le ha2 (not_le.mp h818).le h809
  · -- right
    by_cases h819 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h820 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        by_cases h821 : z ≤ ((10969/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B007.c142_pos (not_le.mp h793).le ha2 (not_le.mp h809).le h821
        · -- right
          exact CKLaneC2R.Cells.S02.B007.c143_pos (not_le.mp h793).le ha2 (not_le.mp h821).le h820
      · -- right
        exact CKLaneC2R.Cells.S02.B000.c1_pos (not_le.mp h793).le ha2 (not_le.mp h820).le h819
    · -- right
      by_cases h822 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B000.c6_pos (not_le.mp h793).le ha2 (not_le.mp h819).le h822
      · -- right
        exact CKLaneC2R.Cells.S02.B000.c8_pos (not_le.mp h793).le ha2 (not_le.mp h822).le h792

theorem strip2_s078 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) (h717 : ¬ (a ≤ ((19/40 : ℚ) : ℝ))) (h792 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h823 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h824 : a ≤ ((39/80 : ℚ) : ℝ)
  · -- left
    by_cases h825 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h826 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B000.c14_pos (not_le.mp h717).le h824 (not_le.mp h792).le h826
      · -- right
        exact CKLaneC2R.Cells.S02.B000.c16_pos (not_le.mp h717).le h824 (not_le.mp h826).le h825
    · -- right
      by_cases h827 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B001.c20_pos (not_le.mp h717).le h824 (not_le.mp h825).le h827
      · -- right
        exact CKLaneC2R.Cells.S02.B001.c22_pos (not_le.mp h717).le h824 (not_le.mp h827).le h823
  · -- right
    by_cases h828 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h829 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B000.c15_pos (not_le.mp h824).le ha2 (not_le.mp h792).le h829
      · -- right
        exact CKLaneC2R.Cells.S02.B000.c17_pos (not_le.mp h824).le ha2 (not_le.mp h829).le h828
    · -- right
      by_cases h830 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B001.c21_pos (not_le.mp h824).le ha2 (not_le.mp h828).le h830
      · -- right
        exact CKLaneC2R.Cells.S02.B001.c23_pos (not_le.mp h824).le ha2 (not_le.mp h830).le h823

end CKLaneC2R.CompactCover


