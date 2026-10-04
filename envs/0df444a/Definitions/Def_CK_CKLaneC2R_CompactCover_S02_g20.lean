-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g20
-- name    : CK_CKLaneC2R_CompactCover_S02_g20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T19:55:31.319064+00:00
-- url     : https://prove2.me/theorems/816252c9-1dd5-4f02-aa7c-542d7328e2d1
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
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B025

namespace CKLaneC2R.CompactCover

theorem strip2_s032 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : a ≤ ((3/8 : ℚ) : ℝ)) (h316 : a ≤ ((29/80 : ℚ) : ℝ)) (h317 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h348 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h356 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h357 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h358 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B011.c230_pos (not_le.mp h1).le h316 (not_le.mp h348).le h358
    · -- right
      exact CKLaneC2R.Cells.S02.B011.c231_pos (not_le.mp h1).le h316 (not_le.mp h358).le h357
  · -- right
    by_cases h359 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B011.c238_pos (not_le.mp h1).le h316 (not_le.mp h357).le h359
    · -- right
      by_cases h360 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B025.c517_pos (not_le.mp h1).le h316 (not_le.mp h359).le h360
      · -- right
        exact CKLaneC2R.Cells.S02.B025.c518_pos (not_le.mp h1).le h316 (not_le.mp h360).le h356

end CKLaneC2R.CompactCover


