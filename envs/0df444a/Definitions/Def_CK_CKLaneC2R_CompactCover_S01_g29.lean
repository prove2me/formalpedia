-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g29
-- name    : CK_CKLaneC2R_CompactCover_S01_g29
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T04:21:24.6797+00:00
-- url     : https://prove2.me/theorems/6efb8205-0284-459c-9154-26c5b3aa6eb5
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B035
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B009

namespace CKLaneC2R.CompactCover

theorem strip1_s036 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : ¬ (a ≤ ((7/32 : ℚ) : ℝ))) (h324 : z ≤ ((217/400 : ℚ) : ℝ)) (h325 : ¬ (a ≤ ((71/320 : ℚ) : ℝ))) (h351 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h352 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h363 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h364 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h365 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B035.c700_pos (not_le.mp h325).le h1 (not_le.mp h352).le h365
      · -- right
        exact CKLaneC2R.Cells.S01.B035.c702_pos (not_le.mp h325).le h1 (not_le.mp h365).le h364
    · -- right
      by_cases h366 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B035.c708_pos (not_le.mp h325).le h1 (not_le.mp h364).le h366
      · -- right
        exact CKLaneC2R.Cells.S01.B035.c710_pos (not_le.mp h325).le h1 (not_le.mp h366).le h363
  · -- right
    by_cases h367 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h368 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B035.c719_pos (not_le.mp h325).le h1 (not_le.mp h363).le h368
      · -- right
        exact CKLaneC2R.Cells.S01.B036.c720_pos (not_le.mp h325).le h1 (not_le.mp h368).le h367
    · -- right
      exact CKLaneC2R.Cells.S01.B009.c183_pos (not_le.mp h325).le h1 (not_le.mp h367).le h351

end CKLaneC2R.CompactCover


