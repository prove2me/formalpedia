-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g32
-- name    : CK_CKLaneC2R_CompactCover_S02_g32
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T05:51:31.214178+00:00
-- url     : https://prove2.me/theorems/ec41f250-8553-4e14-bce6-3dc04ff0dcc1
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B012

namespace CKLaneC2R.CompactCover

theorem strip2_s049 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : ¬ (a ≤ ((3/8 : ℚ) : ℝ))) (h430 : ¬ (a ≤ ((31/80 : ℚ) : ℝ))) (h484 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h510 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h511 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h512 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h513 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B008.c172_pos (not_le.mp h430).le h0 (not_le.mp h484).le h513
      · -- right
        exact CKLaneC2R.Cells.S02.B008.c173_pos (not_le.mp h430).le h0 (not_le.mp h513).le h512
    · -- right
      by_cases h514 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B008.c176_pos (not_le.mp h430).le h0 (not_le.mp h512).le h514
      · -- right
        exact CKLaneC2R.Cells.S02.B008.c177_pos (not_le.mp h430).le h0 (not_le.mp h514).le h511
  · -- right
    by_cases h515 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h516 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B009.c188_pos (not_le.mp h430).le h0 (not_le.mp h511).le h516
      · -- right
        exact CKLaneC2R.Cells.S02.B009.c189_pos (not_le.mp h430).le h0 (not_le.mp h516).le h515
    · -- right
      by_cases h517 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B009.c192_pos (not_le.mp h430).le h0 (not_le.mp h515).le h517
      · -- right
        exact CKLaneC2R.Cells.S02.B009.c193_pos (not_le.mp h430).le h0 (not_le.mp h517).le h510

theorem strip2_s050 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : ¬ (a ≤ ((3/8 : ℚ) : ℝ))) (h430 : ¬ (a ≤ ((31/80 : ℚ) : ℝ))) (h484 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h510 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h518 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h519 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h520 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B011.c236_pos (not_le.mp h430).le h0 (not_le.mp h510).le h520
    · -- right
      exact CKLaneC2R.Cells.S02.B011.c237_pos (not_le.mp h430).le h0 (not_le.mp h520).le h519
  · -- right
    by_cases h521 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B012.c242_pos (not_le.mp h430).le h0 (not_le.mp h519).le h521
    · -- right
      exact CKLaneC2R.Cells.S02.B012.c244_pos (not_le.mp h430).le h0 (not_le.mp h521).le h518

end CKLaneC2R.CompactCover


