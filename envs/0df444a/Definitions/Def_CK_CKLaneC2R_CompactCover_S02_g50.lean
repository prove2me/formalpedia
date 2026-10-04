-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g50
-- name    : CK_CKLaneC2R_CompactCover_S02_g50
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:48:42.971065+00:00
-- url     : https://prove2.me/theorems/84de45c7-63b3-452f-8333-297e86e10fef
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B011

namespace CKLaneC2R.CompactCover

theorem strip2_s073 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) (h717 : a ≤ ((19/40 : ℚ) : ℝ)) (h718 : ¬ (a ≤ ((37/80 : ℚ) : ℝ))) (h756 : z ≤ ((217/400 : ℚ) : ℝ)) (h757 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h769 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h770 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h771 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B006.c134_pos (not_le.mp h718).le h717 (not_le.mp h757).le h771
      · -- right
        exact CKLaneC2R.Cells.S02.B006.c135_pos (not_le.mp h718).le h717 (not_le.mp h771).le h770
    · -- right
      by_cases h772 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B006.c138_pos (not_le.mp h718).le h717 (not_le.mp h770).le h772
      · -- right
        exact CKLaneC2R.Cells.S02.B006.c139_pos (not_le.mp h718).le h717 (not_le.mp h772).le h769
  · -- right
    by_cases h773 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B000.c2_pos (not_le.mp h718).le h717 (not_le.mp h769).le h773
    · -- right
      exact CKLaneC2R.Cells.S02.B000.c4_pos (not_le.mp h718).le h717 (not_le.mp h773).le h756

theorem strip2_s074 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) (h717 : a ≤ ((19/40 : ℚ) : ℝ)) (h718 : ¬ (a ≤ ((37/80 : ℚ) : ℝ))) (h756 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h774 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h775 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h776 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B000.c11_pos (not_le.mp h718).le h717 (not_le.mp h756).le h776
    · -- right
      exact CKLaneC2R.Cells.S02.B000.c13_pos (not_le.mp h718).le h717 (not_le.mp h776).le h775
  · -- right
    by_cases h777 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B000.c19_pos (not_le.mp h718).le h717 (not_le.mp h775).le h777
    · -- right
      by_cases h778 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B011.c226_pos (not_le.mp h718).le h717 (not_le.mp h777).le h778
      · -- right
        exact CKLaneC2R.Cells.S02.B011.c227_pos (not_le.mp h718).le h717 (not_le.mp h778).le h774

end CKLaneC2R.CompactCover


