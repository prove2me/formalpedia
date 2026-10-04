-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g41
-- name    : CK_CKLaneC2R_CompactCover_S02_g41
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T06:50:30.663986+00:00
-- url     : https://prove2.me/theorems/1dfcdba3-e779-48de-9cb2-45f4ecf8253f
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B011

namespace CKLaneC2R.CompactCover

theorem strip2_s061 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : ¬ (a ≤ ((17/40 : ℚ) : ℝ))) (h630 : a ≤ ((7/16 : ℚ) : ℝ)) (h631 : z ≤ ((217/400 : ℚ) : ℝ)) (h632 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h646 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h647 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h648 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B005.c108_pos (not_le.mp h535).le h630 (not_le.mp h632).le h648
      · -- right
        exact CKLaneC2R.Cells.S02.B005.c109_pos (not_le.mp h535).le h630 (not_le.mp h648).le h647
    · -- right
      by_cases h649 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B005.c112_pos (not_le.mp h535).le h630 (not_le.mp h647).le h649
      · -- right
        exact CKLaneC2R.Cells.S02.B005.c113_pos (not_le.mp h535).le h630 (not_le.mp h649).le h646
  · -- right
    by_cases h650 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h651 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B006.c124_pos (not_le.mp h535).le h630 (not_le.mp h646).le h651
      · -- right
        exact CKLaneC2R.Cells.S02.B006.c125_pos (not_le.mp h535).le h630 (not_le.mp h651).le h650
    · -- right
      by_cases h652 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B006.c128_pos (not_le.mp h535).le h630 (not_le.mp h650).le h652
      · -- right
        exact CKLaneC2R.Cells.S02.B006.c129_pos (not_le.mp h535).le h630 (not_le.mp h652).le h631

theorem strip2_s062 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : ¬ (a ≤ ((17/40 : ℚ) : ℝ))) (h630 : a ≤ ((7/16 : ℚ) : ℝ)) (h631 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h653 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h654 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h655 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h656 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B010.c202_pos (not_le.mp h535).le h630 (not_le.mp h631).le h656
      · -- right
        exact CKLaneC2R.Cells.S02.B010.c203_pos (not_le.mp h535).le h630 (not_le.mp h656).le h655
    · -- right
      by_cases h657 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B010.c204_pos (not_le.mp h535).le h630 (not_le.mp h655).le h657
      · -- right
        exact CKLaneC2R.Cells.S02.B010.c205_pos (not_le.mp h535).le h630 (not_le.mp h657).le h654
  · -- right
    by_cases h658 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h659 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B010.c216_pos (not_le.mp h535).le h630 (not_le.mp h654).le h659
      · -- right
        exact CKLaneC2R.Cells.S02.B010.c217_pos (not_le.mp h535).le h630 (not_le.mp h659).le h658
    · -- right
      by_cases h660 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B011.c220_pos (not_le.mp h535).le h630 (not_le.mp h658).le h660
      · -- right
        exact CKLaneC2R.Cells.S02.B011.c221_pos (not_le.mp h535).le h630 (not_le.mp h660).le h653

end CKLaneC2R.CompactCover


