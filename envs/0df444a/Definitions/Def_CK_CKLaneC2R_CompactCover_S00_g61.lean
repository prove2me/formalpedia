-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g61
-- name    : CK_CKLaneC2R_CompactCover_S00_g61
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T18:41:35.283535+00:00
-- url     : https://prove2.me/theorems/7070a8a6-3429-4096-bc3c-9ce6ee3b15b9
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B059
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B060
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B035

namespace CKLaneC2R.CompactCover

theorem strip0_s073 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : ¬ (a ≤ ((11/64 : ℚ) : ℝ))) (h794 : z ≤ ((217/400 : ℚ) : ℝ)) (h795 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h796 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h797 : z ≤ ((2289/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h798 : a ≤ ((111/640 : ℚ) : ℝ)
  · -- left
    by_cases h799 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h800 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h801 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B058.c1167_pos (not_le.mp h693).le h798 hz1 h801
        · -- right
          exact CKLaneC2R.Cells.S00.B058.c1169_pos (not_le.mp h693).le h798 (not_le.mp h801).le h800
      · -- right
        by_cases h802 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B058.c1175_pos (not_le.mp h693).le h798 (not_le.mp h800).le h802
        · -- right
          exact CKLaneC2R.Cells.S00.B058.c1177_pos (not_le.mp h693).le h798 (not_le.mp h802).le h799
    · -- right
      by_cases h803 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h804 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B059.c1199_pos (not_le.mp h693).le h798 (not_le.mp h799).le h804
        · -- right
          exact CKLaneC2R.Cells.S00.B060.c1201_pos (not_le.mp h693).le h798 (not_le.mp h804).le h803
      · -- right
        by_cases h805 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B060.c1207_pos (not_le.mp h693).le h798 (not_le.mp h803).le h805
        · -- right
          exact CKLaneC2R.Cells.S00.B060.c1209_pos (not_le.mp h693).le h798 (not_le.mp h805).le h797
  · -- right
    by_cases h806 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h807 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h808 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B058.c1168_pos (not_le.mp h798).le h0 hz1 h808
        · -- right
          exact CKLaneC2R.Cells.S00.B058.c1170_pos (not_le.mp h798).le h0 (not_le.mp h808).le h807
      · -- right
        by_cases h809 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B058.c1176_pos (not_le.mp h798).le h0 (not_le.mp h807).le h809
        · -- right
          exact CKLaneC2R.Cells.S00.B058.c1178_pos (not_le.mp h798).le h0 (not_le.mp h809).le h806
    · -- right
      by_cases h810 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h811 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B060.c1200_pos (not_le.mp h798).le h0 (not_le.mp h806).le h811
        · -- right
          exact CKLaneC2R.Cells.S00.B060.c1202_pos (not_le.mp h798).le h0 (not_le.mp h811).le h810
      · -- right
        by_cases h812 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B060.c1208_pos (not_le.mp h798).le h0 (not_le.mp h810).le h812
        · -- right
          exact CKLaneC2R.Cells.S00.B060.c1210_pos (not_le.mp h798).le h0 (not_le.mp h812).le h797

theorem strip0_s074 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : ¬ (a ≤ ((11/64 : ℚ) : ℝ))) (h794 : z ≤ ((217/400 : ℚ) : ℝ)) (h795 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h796 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h797 : ¬ (z ≤ ((2289/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h813 : z ≤ ((5491/32000 : ℚ) : ℝ)
  · -- left
    by_cases h814 : z ≤ ((10069/64000 : ℚ) : ℝ)
    · -- left
      by_cases h815 : z ≤ ((769/5120 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B034.c695_pos (not_le.mp h693).le h0 (not_le.mp h797).le h815
      · -- right
        exact CKLaneC2R.Cells.S00.B034.c696_pos (not_le.mp h693).le h0 (not_le.mp h815).le h814
    · -- right
      by_cases h816 : z ≤ ((21051/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B034.c699_pos (not_le.mp h693).le h0 (not_le.mp h814).le h816
      · -- right
        exact CKLaneC2R.Cells.S00.B035.c700_pos (not_le.mp h693).le h0 (not_le.mp h816).le h813
  · -- right
    by_cases h817 : z ≤ ((2379/12800 : ℚ) : ℝ)
    · -- left
      by_cases h818 : z ≤ ((22877/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B035.c705_pos (not_le.mp h693).le h0 (not_le.mp h813).le h818
      · -- right
        exact CKLaneC2R.Cells.S00.B035.c706_pos (not_le.mp h693).le h0 (not_le.mp h818).le h817
    · -- right
      by_cases h819 : a ≤ ((111/640 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B035.c707_pos (not_le.mp h693).le h819 (not_le.mp h817).le h796
      · -- right
        exact CKLaneC2R.Cells.S00.B035.c708_pos (not_le.mp h819).le h0 (not_le.mp h817).le h796

end CKLaneC2R.CompactCover


