-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g26
-- name    : CK_CKLaneC2R_CompactCover_S01_g26
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T02:49:59.726977+00:00
-- url     : https://prove2.me/theorems/0f84d66e-c1d9-46b9-805c-17568998f867
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B035
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B009

namespace CKLaneC2R.CompactCover

theorem strip1_s033 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : ¬ (a ≤ ((7/32 : ℚ) : ℝ))) (h324 : z ≤ ((217/400 : ℚ) : ℝ)) (h325 : a ≤ ((71/320 : ℚ) : ℝ)) (h326 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h327 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h338 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h339 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h340 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B034.c699_pos (not_le.mp h224).le h325 (not_le.mp h327).le h340
      · -- right
        exact CKLaneC2R.Cells.S01.B035.c701_pos (not_le.mp h224).le h325 (not_le.mp h340).le h339
    · -- right
      by_cases h341 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B035.c707_pos (not_le.mp h224).le h325 (not_le.mp h339).le h341
      · -- right
        exact CKLaneC2R.Cells.S01.B035.c709_pos (not_le.mp h224).le h325 (not_le.mp h341).le h338
  · -- right
    by_cases h342 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h343 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B035.c717_pos (not_le.mp h224).le h325 (not_le.mp h338).le h343
      · -- right
        exact CKLaneC2R.Cells.S01.B035.c718_pos (not_le.mp h224).le h325 (not_le.mp h343).le h342
    · -- right
      exact CKLaneC2R.Cells.S01.B009.c182_pos (not_le.mp h224).le h325 (not_le.mp h342).le h326

end CKLaneC2R.CompactCover


