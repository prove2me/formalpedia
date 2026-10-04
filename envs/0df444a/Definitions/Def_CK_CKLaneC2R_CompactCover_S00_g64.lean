-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g64
-- name    : CK_CKLaneC2R_CompactCover_S00_g64
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T12:35:24.393986+00:00
-- url     : https://prove2.me/theorems/f44b2c15-76d8-422f-b3a6-489952d5e57f
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B022
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B023

namespace CKLaneC2R.CompactCover

theorem strip0_s077 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : ¬ (a ≤ ((11/64 : ℚ) : ℝ))) (h794 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h845 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h846 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h847 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h848 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        by_cases h849 : z ≤ ((35633/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B019.c387_pos (not_le.mp h693).le h0 (not_le.mp h794).le h849
        · -- right
          exact CKLaneC2R.Cells.S00.B019.c388_pos (not_le.mp h693).le h0 (not_le.mp h849).le h848
      · -- right
        by_cases h850 : z ≤ ((37459/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B019.c391_pos (not_le.mp h693).le h0 (not_le.mp h848).le h850
        · -- right
          exact CKLaneC2R.Cells.S00.B019.c392_pos (not_le.mp h693).le h0 (not_le.mp h850).le h847
    · -- right
      by_cases h851 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        by_cases h852 : z ≤ ((7857/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B020.c403_pos (not_le.mp h693).le h0 (not_le.mp h847).le h852
        · -- right
          exact CKLaneC2R.Cells.S00.B020.c404_pos (not_le.mp h693).le h0 (not_le.mp h852).le h851
      · -- right
        by_cases h853 : z ≤ ((41111/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B020.c407_pos (not_le.mp h693).le h0 (not_le.mp h851).le h853
        · -- right
          exact CKLaneC2R.Cells.S00.B020.c408_pos (not_le.mp h693).le h0 (not_le.mp h853).le h846
  · -- right
    by_cases h854 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h855 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        by_cases h856 : z ≤ ((42937/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B022.c451_pos (not_le.mp h693).le h0 (not_le.mp h846).le h856
        · -- right
          exact CKLaneC2R.Cells.S00.B022.c452_pos (not_le.mp h693).le h0 (not_le.mp h856).le h855
      · -- right
        by_cases h857 : z ≤ ((44763/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B022.c455_pos (not_le.mp h693).le h0 (not_le.mp h855).le h857
        · -- right
          exact CKLaneC2R.Cells.S00.B022.c456_pos (not_le.mp h693).le h0 (not_le.mp h857).le h854
    · -- right
      by_cases h858 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h859 : z ≤ ((46589/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B023.c467_pos (not_le.mp h693).le h0 (not_le.mp h854).le h859
        · -- right
          exact CKLaneC2R.Cells.S00.B023.c468_pos (not_le.mp h693).le h0 (not_le.mp h859).le h858
      · -- right
        by_cases h860 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B023.c471_pos (not_le.mp h693).le h0 (not_le.mp h858).le h860
        · -- right
          exact CKLaneC2R.Cells.S00.B023.c472_pos (not_le.mp h693).le h0 (not_le.mp h860).le h845

end CKLaneC2R.CompactCover


