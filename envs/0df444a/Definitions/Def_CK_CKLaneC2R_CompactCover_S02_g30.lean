-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g30
-- name    : CK_CKLaneC2R_CompactCover_S02_g30
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T13:13:44.424249+00:00
-- url     : https://prove2.me/theorems/fec271f2-3810-4447-81c6-72a96fd52ab7
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B019

namespace CKLaneC2R.CompactCover

theorem strip2_s046 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : ¬ (a ≤ ((3/8 : ℚ) : ℝ))) (h430 : ¬ (a ≤ ((31/80 : ℚ) : ℝ))) (h484 : z ≤ ((217/400 : ℚ) : ℝ)) (h485 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h486 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h487 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h488 : a ≤ ((63/160 : ℚ) : ℝ)
    · -- left
      by_cases h489 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h490 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B032.c655_pos (not_le.mp h430).le h488 hz1 h490
        · -- right
          exact CKLaneC2R.Cells.S02.B032.c657_pos (not_le.mp h430).le h488 (not_le.mp h490).le h489
      · -- right
        by_cases h491 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B033.c663_pos (not_le.mp h430).le h488 (not_le.mp h489).le h491
        · -- right
          exact CKLaneC2R.Cells.S02.B033.c665_pos (not_le.mp h430).le h488 (not_le.mp h491).le h487
    · -- right
      by_cases h492 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h493 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B032.c656_pos (not_le.mp h488).le h0 hz1 h493
        · -- right
          exact CKLaneC2R.Cells.S02.B032.c658_pos (not_le.mp h488).le h0 (not_le.mp h493).le h492
      · -- right
        by_cases h494 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B033.c664_pos (not_le.mp h488).le h0 (not_le.mp h492).le h494
        · -- right
          exact CKLaneC2R.Cells.S02.B033.c666_pos (not_le.mp h488).le h0 (not_le.mp h494).le h487
  · -- right
    by_cases h495 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h496 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B018.c375_pos (not_le.mp h430).le h0 (not_le.mp h487).le h496
      · -- right
        exact CKLaneC2R.Cells.S02.B018.c376_pos (not_le.mp h430).le h0 (not_le.mp h496).le h495
    · -- right
      by_cases h497 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B018.c379_pos (not_le.mp h430).le h0 (not_le.mp h495).le h497
      · -- right
        exact CKLaneC2R.Cells.S02.B019.c380_pos (not_le.mp h430).le h0 (not_le.mp h497).le h486

end CKLaneC2R.CompactCover


