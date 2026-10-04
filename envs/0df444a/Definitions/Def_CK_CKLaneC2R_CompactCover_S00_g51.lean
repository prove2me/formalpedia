-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g51
-- name    : CK_CKLaneC2R_CompactCover_S00_g51
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T20:05:32.009859+00:00
-- url     : https://prove2.me/theorems/719dc621-b00e-44d0-bfef-e8ba71d769da
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B050

namespace CKLaneC2R.CompactCover

theorem strip0_s062 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : ¬ (a ≤ ((53/320 : ℚ) : ℝ))) (h590 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h645 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h661 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h669 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h676 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h677 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    by_cases h678 : z ≤ ((121481/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B050.c1007_pos (not_le.mp h482).le h481 (not_le.mp h669).le h678
    · -- right
      exact CKLaneC2R.Cells.S00.B050.c1009_pos (not_le.mp h482).le h481 (not_le.mp h678).le h677
  · -- right
    by_cases h679 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B050.c1015_pos (not_le.mp h482).le h481 (not_le.mp h677).le h679
    · -- right
      exact CKLaneC2R.Cells.S00.B050.c1017_pos (not_le.mp h482).le h481 (not_le.mp h679).le h676

end CKLaneC2R.CompactCover


