-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g47
-- name    : CK_CKLaneC2R_CompactCover_S02_g47
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T13:42:27.623859+00:00
-- url     : https://prove2.me/theorems/3ee6510f-55cf-46b1-8273-b2f69348ece1
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
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B011

namespace CKLaneC2R.CompactCover

theorem strip2_s069 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) (h717 : a ≤ ((19/40 : ℚ) : ℝ)) (h718 : a ≤ ((37/80 : ℚ) : ℝ)) (h719 : z ≤ ((217/400 : ℚ) : ℝ)) (h720 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h732 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h733 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h734 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B006.c132_pos (not_le.mp h534).le h718 (not_le.mp h720).le h734
      · -- right
        exact CKLaneC2R.Cells.S02.B006.c133_pos (not_le.mp h534).le h718 (not_le.mp h734).le h733
    · -- right
      by_cases h735 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B006.c136_pos (not_le.mp h534).le h718 (not_le.mp h733).le h735
      · -- right
        exact CKLaneC2R.Cells.S02.B006.c137_pos (not_le.mp h534).le h718 (not_le.mp h735).le h732
  · -- right
    by_cases h736 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h737 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B007.c144_pos (not_le.mp h534).le h718 (not_le.mp h732).le h737
      · -- right
        exact CKLaneC2R.Cells.S02.B007.c145_pos (not_le.mp h534).le h718 (not_le.mp h737).le h736
    · -- right
      exact CKLaneC2R.Cells.S02.B000.c3_pos (not_le.mp h534).le h718 (not_le.mp h736).le h719

theorem strip2_s070 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) (h717 : a ≤ ((19/40 : ℚ) : ℝ)) (h718 : a ≤ ((37/80 : ℚ) : ℝ)) (h719 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h738 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h739 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h740 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B000.c10_pos (not_le.mp h534).le h718 (not_le.mp h719).le h740
    · -- right
      exact CKLaneC2R.Cells.S02.B000.c12_pos (not_le.mp h534).le h718 (not_le.mp h740).le h739
  · -- right
    by_cases h741 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B000.c18_pos (not_le.mp h534).le h718 (not_le.mp h739).le h741
    · -- right
      by_cases h742 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B011.c224_pos (not_le.mp h534).le h718 (not_le.mp h741).le h742
      · -- right
        exact CKLaneC2R.Cells.S02.B011.c225_pos (not_le.mp h534).le h718 (not_le.mp h742).le h738

end CKLaneC2R.CompactCover


