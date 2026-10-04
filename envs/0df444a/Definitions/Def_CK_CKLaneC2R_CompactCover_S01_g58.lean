-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g58
-- name    : CK_CKLaneC2R_CompactCover_S01_g58
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T10:11:05.303604+00:00
-- url     : https://prove2.me/theorems/fdcb94f1-bd19-4da7-8457-759057ba02f3
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B030

namespace CKLaneC2R.CompactCover

theorem strip1_s082 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : a ≤ ((41/160 : ℚ) : ℝ)) (h749 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h787 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h795 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h801 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h802 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h803 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B029.c591_pos (not_le.mp h0).le h748 (not_le.mp h795).le h803
    · -- right
      exact CKLaneC2R.Cells.S01.B029.c592_pos (not_le.mp h0).le h748 (not_le.mp h803).le h802
  · -- right
    by_cases h804 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B029.c599_pos (not_le.mp h0).le h748 (not_le.mp h802).le h804
    · -- right
      exact CKLaneC2R.Cells.S01.B030.c601_pos (not_le.mp h0).le h748 (not_le.mp h804).le h801

end CKLaneC2R.CompactCover


