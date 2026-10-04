-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g59
-- name    : CK_CKLaneC2R_CompactCover_S01_g59
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T20:09:03.523712+00:00
-- url     : https://prove2.me/theorems/84053a9c-26cc-46ab-872c-de6ffd970ba8
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B045
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B046
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B057
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B059

namespace CKLaneC2R.CompactCover

theorem strip1_s083 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : a ≤ ((41/160 : ℚ) : ℝ)) (h749 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h787 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h795 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h801 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h805 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h806 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h807 : z ≤ ((121481/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B045.c913_pos (not_le.mp h0).le h748 (not_le.mp h801).le h807
      · -- right
        exact CKLaneC2R.Cells.S01.B045.c914_pos (not_le.mp h0).le h748 (not_le.mp h807).le h806
    · -- right
      by_cases h808 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B045.c915_pos (not_le.mp h0).le h748 (not_le.mp h806).le h808
      · -- right
        exact CKLaneC2R.Cells.S01.B045.c916_pos (not_le.mp h0).le h748 (not_le.mp h808).le h805
  · -- right
    by_cases h809 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h810 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B046.c933_pos (not_le.mp h0).le h748 (not_le.mp h805).le h810
      · -- right
        exact CKLaneC2R.Cells.S01.B046.c935_pos (not_le.mp h0).le h748 (not_le.mp h810).le h809
    · -- right
      by_cases h811 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h812 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B055.c1108_pos (not_le.mp h0).le h748 (not_le.mp h809).le h812
        · -- right
          exact CKLaneC2R.Cells.S01.B055.c1110_pos (not_le.mp h0).le h748 (not_le.mp h812).le h811
      · -- right
        by_cases h813 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          by_cases h814 : z ≤ ((508749/512000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B057.c1153_pos (not_le.mp h0).le h748 (not_le.mp h811).le h814
          · -- right
            exact CKLaneC2R.Cells.S01.B057.c1154_pos (not_le.mp h0).le h748 (not_le.mp h814).le h813
        · -- right
          by_cases h815 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B058.c1163_pos (not_le.mp h0).le h748 (not_le.mp h813).le h815
          · -- right
            by_cases h816 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B059.c1190_pos (not_le.mp h0).le h748 (not_le.mp h815).le h816
            · -- right
              exact CKLaneC2R.Cells.S01.B059.c1192_pos (not_le.mp h0).le h748 (not_le.mp h816).le hz2

end CKLaneC2R.CompactCover


