-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g31
-- name    : CK_CKLaneC2R_CompactCover_S00_g31
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T01:46:00.453445+00:00
-- url     : https://prove2.me/theorems/3222f9a4-3ca8-400f-bad1-8ba132ad22e2
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B038

namespace CKLaneC2R.CompactCover

theorem strip0_s037 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : ¬ (a ≤ ((51/320 : ℚ) : ℝ))) (h369 : z ≤ ((217/400 : ℚ) : ℝ)) (h370 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h371 : a ≤ ((103/640 : ℚ) : ℝ)) (h372 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h387 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h388 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h389 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B036.c729_pos (not_le.mp h253).le h371 (not_le.mp h372).le h389
      · -- right
        exact CKLaneC2R.Cells.S00.B036.c731_pos (not_le.mp h253).le h371 (not_le.mp h389).le h388
    · -- right
      by_cases h390 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B036.c737_pos (not_le.mp h253).le h371 (not_le.mp h388).le h390
      · -- right
        exact CKLaneC2R.Cells.S00.B036.c739_pos (not_le.mp h253).le h371 (not_le.mp h390).le h387
  · -- right
    by_cases h391 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h392 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B038.c761_pos (not_le.mp h253).le h371 (not_le.mp h387).le h392
      · -- right
        exact CKLaneC2R.Cells.S00.B038.c763_pos (not_le.mp h253).le h371 (not_le.mp h392).le h391
    · -- right
      by_cases h393 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B038.c769_pos (not_le.mp h253).le h371 (not_le.mp h391).le h393
      · -- right
        exact CKLaneC2R.Cells.S00.B038.c771_pos (not_le.mp h253).le h371 (not_le.mp h393).le h370

end CKLaneC2R.CompactCover


