-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g23
-- name    : CK_CKLaneC2R_CompactCover_S03_g23
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T07:03:41.192142+00:00
-- url     : https://prove2.me/theorems/6d406541-3a4d-400f-9b33-63c9117627a6
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S03 (proof part of strip3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S03 (proof part of strip3).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B003
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B007

namespace CKLaneC2R.CompactCover

theorem strip3_s032 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((3/5 : ℚ) : ℝ))) (h220 : ¬ (a ≤ ((13/20 : ℚ) : ℝ))) (h313 : ¬ (a ≤ ((27/40 : ℚ) : ℝ))) (h357 : z ≤ ((217/400 : ℚ) : ℝ)) (h358 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h370 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h371 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h372 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B003.c71_pos (not_le.mp h313).le ha2 (not_le.mp h358).le h372
      · -- right
        exact CKLaneC2R.Cells.S03.B003.c72_pos (not_le.mp h313).le ha2 (not_le.mp h372).le h371
    · -- right
      by_cases h373 : a ≤ ((11/16 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B003.c73_pos (not_le.mp h313).le h373 (not_le.mp h371).le h370
      · -- right
        exact CKLaneC2R.Cells.S03.B003.c74_pos (not_le.mp h373).le ha2 (not_le.mp h371).le h370
  · -- right
    by_cases h374 : a ≤ ((11/16 : ℚ) : ℝ)
    · -- left
      by_cases h375 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B003.c79_pos (not_le.mp h313).le h374 (not_le.mp h370).le h375
      · -- right
        exact CKLaneC2R.Cells.S03.B004.c81_pos (not_le.mp h313).le h374 (not_le.mp h375).le h357
    · -- right
      by_cases h376 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B004.c80_pos (not_le.mp h374).le ha2 (not_le.mp h370).le h376
      · -- right
        exact CKLaneC2R.Cells.S03.B004.c82_pos (not_le.mp h374).le ha2 (not_le.mp h376).le h357

theorem strip3_s033 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((3/5 : ℚ) : ℝ))) (h220 : ¬ (a ≤ ((13/20 : ℚ) : ℝ))) (h313 : ¬ (a ≤ ((27/40 : ℚ) : ℝ))) (h357 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h377 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h378 : a ≤ ((11/16 : ℚ) : ℝ)
  · -- left
    by_cases h379 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h380 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B006.c135_pos (not_le.mp h313).le h378 (not_le.mp h357).le h380
      · -- right
        exact CKLaneC2R.Cells.S03.B006.c137_pos (not_le.mp h313).le h378 (not_le.mp h380).le h379
    · -- right
      by_cases h381 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B007.c143_pos (not_le.mp h313).le h378 (not_le.mp h379).le h381
      · -- right
        exact CKLaneC2R.Cells.S03.B007.c145_pos (not_le.mp h313).le h378 (not_le.mp h381).le h377
  · -- right
    by_cases h382 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h383 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B006.c136_pos (not_le.mp h378).le ha2 (not_le.mp h357).le h383
      · -- right
        exact CKLaneC2R.Cells.S03.B006.c138_pos (not_le.mp h378).le ha2 (not_le.mp h383).le h382
    · -- right
      by_cases h384 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B007.c144_pos (not_le.mp h378).le ha2 (not_le.mp h382).le h384
      · -- right
        exact CKLaneC2R.Cells.S03.B007.c146_pos (not_le.mp h378).le ha2 (not_le.mp h384).le h377

end CKLaneC2R.CompactCover


