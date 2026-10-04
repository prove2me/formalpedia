-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g34
-- name    : CK_CKLaneC2R_CompactCover_S00_g34
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T21:39:22.214485+00:00
-- url     : https://prove2.me/theorems/71f4b5e8-f28a-4116-b79b-2b17185d395b
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B006

namespace CKLaneC2R.CompactCover

theorem strip0_s040 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : ¬ (a ≤ ((51/320 : ℚ) : ℝ))) (h369 : z ≤ ((217/400 : ℚ) : ℝ)) (h370 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h416 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h417 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h418 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h419 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B004.c83_pos (not_le.mp h253).le h1 (not_le.mp h370).le h419
        · -- right
          exact CKLaneC2R.Cells.S00.B004.c84_pos (not_le.mp h253).le h1 (not_le.mp h419).le h418
      · -- right
        by_cases h420 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B004.c87_pos (not_le.mp h253).le h1 (not_le.mp h418).le h420
        · -- right
          exact CKLaneC2R.Cells.S00.B004.c88_pos (not_le.mp h253).le h1 (not_le.mp h420).le h417
    · -- right
      by_cases h421 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h422 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B004.c97_pos (not_le.mp h253).le h1 (not_le.mp h417).le h422
        · -- right
          exact CKLaneC2R.Cells.S00.B004.c98_pos (not_le.mp h253).le h1 (not_le.mp h422).le h421
      · -- right
        by_cases h423 : z ≤ ((26503/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B005.c101_pos (not_le.mp h253).le h1 (not_le.mp h421).le h423
        · -- right
          exact CKLaneC2R.Cells.S00.B005.c102_pos (not_le.mp h253).le h1 (not_le.mp h423).le h416
  · -- right
    by_cases h424 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h425 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        by_cases h426 : z ≤ ((28329/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B005.c113_pos (not_le.mp h253).le h1 (not_le.mp h416).le h426
        · -- right
          exact CKLaneC2R.Cells.S00.B005.c114_pos (not_le.mp h253).le h1 (not_le.mp h426).le h425
      · -- right
        by_cases h427 : z ≤ ((6031/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B005.c117_pos (not_le.mp h253).le h1 (not_le.mp h425).le h427
        · -- right
          exact CKLaneC2R.Cells.S00.B005.c118_pos (not_le.mp h253).le h1 (not_le.mp h427).le h424
    · -- right
      by_cases h428 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        by_cases h429 : z ≤ ((31981/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B006.c129_pos (not_le.mp h253).le h1 (not_le.mp h424).le h429
        · -- right
          exact CKLaneC2R.Cells.S00.B006.c130_pos (not_le.mp h253).le h1 (not_le.mp h429).le h428
      · -- right
        by_cases h430 : z ≤ ((33807/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B006.c133_pos (not_le.mp h253).le h1 (not_le.mp h428).le h430
        · -- right
          exact CKLaneC2R.Cells.S00.B006.c134_pos (not_le.mp h253).le h1 (not_le.mp h430).le h369

end CKLaneC2R.CompactCover


