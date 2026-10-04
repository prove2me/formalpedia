-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g34
-- name    : CK_CKLaneC2R_CompactCover_S01_g34
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T16:10:01.828935+00:00
-- url     : https://prove2.me/theorems/096db0bd-90d2-4428-ad00-8f0191dd3c68
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B050
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B051
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B037

namespace CKLaneC2R.CompactCover

theorem strip1_s042 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : a ≤ ((37/160 : ℚ) : ℝ)) (h421 : z ≤ ((217/400 : ℚ) : ℝ)) (h422 : a ≤ ((73/320 : ℚ) : ℝ)) (h423 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h424 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h425 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h426 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h427 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h428 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B050.c1014_pos (not_le.mp h1).le h422 hz1 h428
        · -- right
          exact CKLaneC2R.Cells.S01.B050.c1016_pos (not_le.mp h1).le h422 (not_le.mp h428).le h427
      · -- right
        by_cases h429 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B050.c1018_pos (not_le.mp h1).le h422 (not_le.mp h427).le h429
        · -- right
          exact CKLaneC2R.Cells.S01.B050.c1019_pos (not_le.mp h1).le h422 (not_le.mp h429).le h426
    · -- right
      by_cases h430 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h431 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B051.c1030_pos (not_le.mp h1).le h422 (not_le.mp h426).le h431
        · -- right
          exact CKLaneC2R.Cells.S01.B051.c1031_pos (not_le.mp h1).le h422 (not_le.mp h431).le h430
      · -- right
        exact CKLaneC2R.Cells.S01.B036.c721_pos (not_le.mp h1).le h422 (not_le.mp h430).le h425
  · -- right
    by_cases h432 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h433 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B036.c734_pos (not_le.mp h1).le h422 (not_le.mp h425).le h433
      · -- right
        exact CKLaneC2R.Cells.S01.B036.c736_pos (not_le.mp h1).le h422 (not_le.mp h433).le h432
    · -- right
      by_cases h434 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B037.c742_pos (not_le.mp h1).le h422 (not_le.mp h432).le h434
      · -- right
        exact CKLaneC2R.Cells.S01.B037.c744_pos (not_le.mp h1).le h422 (not_le.mp h434).le h424

end CKLaneC2R.CompactCover


