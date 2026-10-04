-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g40
-- name    : CK_CKLaneC2R_CompactCover_S02_g40
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T01:05:13.027421+00:00
-- url     : https://prove2.me/theorems/66c1e9bc-9ce8-4736-9955-1ed831de7a5f
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B021
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B003

namespace CKLaneC2R.CompactCover

theorem strip2_s060 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : ¬ (a ≤ ((17/40 : ℚ) : ℝ))) (h630 : a ≤ ((7/16 : ℚ) : ℝ)) (h631 : z ≤ ((217/400 : ℚ) : ℝ)) (h632 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h633 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h634 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h635 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h636 : a ≤ ((69/160 : ℚ) : ℝ)
        · -- left
          by_cases h637 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B034.c687_pos (not_le.mp h535).le h636 hz1 h637
          · -- right
            exact CKLaneC2R.Cells.S02.B034.c689_pos (not_le.mp h535).le h636 (not_le.mp h637).le h635
        · -- right
          by_cases h638 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B034.c688_pos (not_le.mp h636).le h630 hz1 h638
          · -- right
            exact CKLaneC2R.Cells.S02.B034.c690_pos (not_le.mp h636).le h630 (not_le.mp h638).le h635
      · -- right
        by_cases h639 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B020.c413_pos (not_le.mp h535).le h630 (not_le.mp h635).le h639
        · -- right
          exact CKLaneC2R.Cells.S02.B020.c414_pos (not_le.mp h535).le h630 (not_le.mp h639).le h634
    · -- right
      by_cases h640 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h641 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B021.c425_pos (not_le.mp h535).le h630 (not_le.mp h634).le h641
        · -- right
          exact CKLaneC2R.Cells.S02.B021.c426_pos (not_le.mp h535).le h630 (not_le.mp h641).le h640
      · -- right
        by_cases h642 : z ≤ ((2379/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B021.c429_pos (not_le.mp h535).le h630 (not_le.mp h640).le h642
        · -- right
          exact CKLaneC2R.Cells.S02.B021.c430_pos (not_le.mp h535).le h630 (not_le.mp h642).le h633
  · -- right
    by_cases h643 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h644 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B003.c71_pos (not_le.mp h535).le h630 (not_le.mp h633).le h644
      · -- right
        exact CKLaneC2R.Cells.S02.B003.c72_pos (not_le.mp h535).le h630 (not_le.mp h644).le h643
    · -- right
      by_cases h645 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B003.c75_pos (not_le.mp h535).le h630 (not_le.mp h643).le h645
      · -- right
        exact CKLaneC2R.Cells.S02.B003.c76_pos (not_le.mp h535).le h630 (not_le.mp h645).le h632

end CKLaneC2R.CompactCover


