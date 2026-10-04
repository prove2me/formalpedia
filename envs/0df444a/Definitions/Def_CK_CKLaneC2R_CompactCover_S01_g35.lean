-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g35
-- name    : CK_CKLaneC2R_CompactCover_S01_g35
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T13:55:01.112771+00:00
-- url     : https://prove2.me/theorems/cc1682ce-ba67-4087-b0bd-96c1be7ee788
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B038
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B015

namespace CKLaneC2R.CompactCover

theorem strip1_s043 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : a ≤ ((37/160 : ℚ) : ℝ)) (h421 : z ≤ ((217/400 : ℚ) : ℝ)) (h422 : a ≤ ((73/320 : ℚ) : ℝ)) (h423 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h424 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h435 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h436 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h437 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B038.c766_pos (not_le.mp h1).le h422 (not_le.mp h424).le h437
      · -- right
        exact CKLaneC2R.Cells.S01.B038.c768_pos (not_le.mp h1).le h422 (not_le.mp h437).le h436
    · -- right
      by_cases h438 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B038.c774_pos (not_le.mp h1).le h422 (not_le.mp h436).le h438
      · -- right
        exact CKLaneC2R.Cells.S01.B038.c776_pos (not_le.mp h1).le h422 (not_le.mp h438).le h435
  · -- right
    by_cases h439 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B009.c185_pos (not_le.mp h1).le h422 (not_le.mp h435).le h439
    · -- right
      exact CKLaneC2R.Cells.S01.B009.c187_pos (not_le.mp h1).le h422 (not_le.mp h439).le h423

theorem strip1_s044 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : a ≤ ((37/160 : ℚ) : ℝ)) (h421 : z ≤ ((217/400 : ℚ) : ℝ)) (h422 : a ≤ ((73/320 : ℚ) : ℝ)) (h423 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h440 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h441 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h442 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B013.c270_pos (not_le.mp h1).le h422 (not_le.mp h423).le h442
      · -- right
        exact CKLaneC2R.Cells.S01.B013.c272_pos (not_le.mp h1).le h422 (not_le.mp h442).le h441
    · -- right
      by_cases h443 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B013.c278_pos (not_le.mp h1).le h422 (not_le.mp h441).le h443
      · -- right
        exact CKLaneC2R.Cells.S01.B014.c280_pos (not_le.mp h1).le h422 (not_le.mp h443).le h440
  · -- right
    by_cases h444 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h445 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B015.c302_pos (not_le.mp h1).le h422 (not_le.mp h440).le h445
      · -- right
        exact CKLaneC2R.Cells.S01.B015.c304_pos (not_le.mp h1).le h422 (not_le.mp h445).le h444
    · -- right
      by_cases h446 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B015.c310_pos (not_le.mp h1).le h422 (not_le.mp h444).le h446
      · -- right
        exact CKLaneC2R.Cells.S01.B015.c312_pos (not_le.mp h1).le h422 (not_le.mp h446).le h421

end CKLaneC2R.CompactCover


