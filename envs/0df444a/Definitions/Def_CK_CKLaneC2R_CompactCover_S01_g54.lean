-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g54
-- name    : CK_CKLaneC2R_CompactCover_S01_g54
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T18:09:13.957128+00:00
-- url     : https://prove2.me/theorems/b737353a-b9de-4ee7-875b-1d6254e882df
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

theorem strip1_s075 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : ¬ (a ≤ ((39/160 : ℚ) : ℝ))) (h675 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h715 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h723 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h730 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h734 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h735 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h736 : z ≤ ((121481/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B045.c907_pos (not_le.mp h598).le h0 (not_le.mp h730).le h736
      · -- right
        exact CKLaneC2R.Cells.S01.B045.c908_pos (not_le.mp h598).le h0 (not_le.mp h736).le h735
    · -- right
      by_cases h737 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B045.c911_pos (not_le.mp h598).le h0 (not_le.mp h735).le h737
      · -- right
        exact CKLaneC2R.Cells.S01.B045.c912_pos (not_le.mp h598).le h0 (not_le.mp h737).le h734
  · -- right
    by_cases h738 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h739 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B046.c931_pos (not_le.mp h598).le h0 (not_le.mp h734).le h739
      · -- right
        exact CKLaneC2R.Cells.S01.B046.c932_pos (not_le.mp h598).le h0 (not_le.mp h739).le h738
    · -- right
      by_cases h740 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h741 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B055.c1105_pos (not_le.mp h598).le h0 (not_le.mp h738).le h741
        · -- right
          exact CKLaneC2R.Cells.S01.B055.c1107_pos (not_le.mp h598).le h0 (not_le.mp h741).le h740
      · -- right
        by_cases h742 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          by_cases h743 : z ≤ ((508749/512000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B057.c1151_pos (not_le.mp h598).le h0 (not_le.mp h740).le h743
          · -- right
            exact CKLaneC2R.Cells.S01.B057.c1152_pos (not_le.mp h598).le h0 (not_le.mp h743).le h742
        · -- right
          by_cases h744 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B058.c1162_pos (not_le.mp h598).le h0 (not_le.mp h742).le h744
          · -- right
            by_cases h745 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B059.c1187_pos (not_le.mp h598).le h0 (not_le.mp h744).le h745
            · -- right
              exact CKLaneC2R.Cells.S01.B059.c1189_pos (not_le.mp h598).le h0 (not_le.mp h745).le hz2

end CKLaneC2R.CompactCover


