-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g58
-- name    : CK_CKLaneC2R_CompactCover_S00_g58
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T04:03:51.659006+00:00
-- url     : https://prove2.me/theorems/339406a3-5c74-41e1-8c9d-802d6dbb8832
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B048

namespace CKLaneC2R.CompactCover

theorem strip0_s069 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : a ≤ ((11/64 : ℚ) : ℝ)) (h694 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h747 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h763 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h764 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h765 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h766 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B027.c541_pos (not_le.mp h481).le h693 (not_le.mp h747).le h766
      · -- right
        exact CKLaneC2R.Cells.S00.B027.c542_pos (not_le.mp h481).le h693 (not_le.mp h766).le h765
    · -- right
      by_cases h767 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B027.c545_pos (not_le.mp h481).le h693 (not_le.mp h765).le h767
      · -- right
        exact CKLaneC2R.Cells.S00.B027.c546_pos (not_le.mp h481).le h693 (not_le.mp h767).le h764
  · -- right
    by_cases h768 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h769 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B028.c565_pos (not_le.mp h481).le h693 (not_le.mp h764).le h769
      · -- right
        exact CKLaneC2R.Cells.S00.B028.c567_pos (not_le.mp h481).le h693 (not_le.mp h769).le h768
    · -- right
      by_cases h770 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B028.c573_pos (not_le.mp h481).le h693 (not_le.mp h768).le h770
      · -- right
        exact CKLaneC2R.Cells.S00.B028.c575_pos (not_le.mp h481).le h693 (not_le.mp h770).le h763

theorem strip0_s070 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : a ≤ ((11/64 : ℚ) : ℝ)) (h694 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h747 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h763 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h771 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h772 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h773 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B032.c641_pos (not_le.mp h481).le h693 (not_le.mp h763).le h773
    · -- right
      exact CKLaneC2R.Cells.S00.B032.c643_pos (not_le.mp h481).le h693 (not_le.mp h773).le h772
  · -- right
    by_cases h774 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      by_cases h775 : z ≤ ((117829/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B048.c973_pos (not_le.mp h481).le h693 (not_le.mp h772).le h775
      · -- right
        exact CKLaneC2R.Cells.S00.B048.c974_pos (not_le.mp h481).le h693 (not_le.mp h775).le h774
    · -- right
      by_cases h776 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B048.c977_pos (not_le.mp h481).le h693 (not_le.mp h774).le h776
      · -- right
        exact CKLaneC2R.Cells.S00.B048.c978_pos (not_le.mp h481).le h693 (not_le.mp h776).le h771

end CKLaneC2R.CompactCover


