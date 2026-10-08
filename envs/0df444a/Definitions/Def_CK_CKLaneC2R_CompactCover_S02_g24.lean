-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g24
-- name    : CK_CKLaneC2R_CompactCover_S02_g24
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T14:09:46.954881+00:00
-- url     : https://prove2.me/theorems/13ec7f90-bdfa-4f84-9e5d-cf1a0c755e37
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B012

namespace CKLaneC2R.CompactCover

theorem strip2_s038 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : a ≤ ((3/8 : ℚ) : ℝ)) (h316 : ¬ (a ≤ ((29/80 : ℚ) : ℝ))) (h375 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h405 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h413 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h414 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h415 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B011.c232_pos (not_le.mp h316).le h315 (not_le.mp h405).le h415
    · -- right
      exact CKLaneC2R.Cells.S02.B011.c233_pos (not_le.mp h316).le h315 (not_le.mp h415).le h414
  · -- right
    by_cases h416 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B011.c239_pos (not_le.mp h316).le h315 (not_le.mp h414).le h416
    · -- right
      exact CKLaneC2R.Cells.S02.B012.c240_pos (not_le.mp h316).le h315 (not_le.mp h416).le h413

end CKLaneC2R.CompactCover


