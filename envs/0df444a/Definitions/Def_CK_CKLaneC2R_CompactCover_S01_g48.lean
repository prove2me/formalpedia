-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g48
-- name    : CK_CKLaneC2R_CompactCover_S01_g48
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T09:28:22.634684+00:00
-- url     : https://prove2.me/theorems/1c1540ca-e1a9-4d17-b3b9-ea82a57a0eef
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B015
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B000

namespace CKLaneC2R.CompactCover

theorem strip1_s063 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : a ≤ ((39/160 : ℚ) : ℝ)) (h599 : z ≤ ((217/400 : ℚ) : ℝ)) (h600 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h629 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h630 : a ≤ ((77/320 : ℚ) : ℝ)
    · -- left
      by_cases h631 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        by_cases h632 : z ≤ ((10969/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B014.c286_pos (not_le.mp h419).le h630 (not_le.mp h600).le h632
        · -- right
          exact CKLaneC2R.Cells.S01.B014.c288_pos (not_le.mp h419).le h630 (not_le.mp h632).le h631
      · -- right
        by_cases h633 : z ≤ ((2559/6400 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B014.c294_pos (not_le.mp h419).le h630 (not_le.mp h631).le h633
        · -- right
          exact CKLaneC2R.Cells.S01.B014.c296_pos (not_le.mp h419).le h630 (not_le.mp h633).le h629
    · -- right
      by_cases h634 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        by_cases h635 : z ≤ ((10969/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B014.c287_pos (not_le.mp h630).le h598 (not_le.mp h600).le h635
        · -- right
          exact CKLaneC2R.Cells.S01.B014.c289_pos (not_le.mp h630).le h598 (not_le.mp h635).le h634
      · -- right
        by_cases h636 : z ≤ ((2559/6400 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B014.c295_pos (not_le.mp h630).le h598 (not_le.mp h634).le h636
        · -- right
          exact CKLaneC2R.Cells.S01.B014.c297_pos (not_le.mp h630).le h598 (not_le.mp h636).le h629
  · -- right
    by_cases h637 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h638 : a ≤ ((77/320 : ℚ) : ℝ)
      · -- left
        by_cases h639 : z ≤ ((14621/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B015.c318_pos (not_le.mp h419).le h638 (not_le.mp h629).le h639
        · -- right
          exact CKLaneC2R.Cells.S01.B016.c320_pos (not_le.mp h419).le h638 (not_le.mp h639).le h637
      · -- right
        by_cases h640 : z ≤ ((14621/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B015.c319_pos (not_le.mp h638).le h598 (not_le.mp h629).le h640
        · -- right
          exact CKLaneC2R.Cells.S01.B016.c321_pos (not_le.mp h638).le h598 (not_le.mp h640).le h637
    · -- right
      by_cases h641 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B000.c2_pos (not_le.mp h419).le h598 (not_le.mp h637).le h641
      · -- right
        exact CKLaneC2R.Cells.S01.B000.c3_pos (not_le.mp h419).le h598 (not_le.mp h641).le h599

end CKLaneC2R.CompactCover


