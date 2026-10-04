-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g65
-- name    : CK_CKLaneC2R_CompactCover_S00_g65
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T17:53:12.503998+00:00
-- url     : https://prove2.me/theorems/097f9a8a-ff88-4d12-95da-7c749917d3f1
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
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B049

namespace CKLaneC2R.CompactCover

theorem strip0_s078 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : ¬ (a ≤ ((11/64 : ℚ) : ℝ))) (h794 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h845 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h861 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h862 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h863 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h864 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B027.c543_pos (not_le.mp h693).le h0 (not_le.mp h845).le h864
      · -- right
        exact CKLaneC2R.Cells.S00.B027.c544_pos (not_le.mp h693).le h0 (not_le.mp h864).le h863
    · -- right
      by_cases h865 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B027.c547_pos (not_le.mp h693).le h0 (not_le.mp h863).le h865
      · -- right
        exact CKLaneC2R.Cells.S00.B027.c548_pos (not_le.mp h693).le h0 (not_le.mp h865).le h862
  · -- right
    by_cases h866 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h867 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B028.c566_pos (not_le.mp h693).le h0 (not_le.mp h862).le h867
      · -- right
        exact CKLaneC2R.Cells.S00.B028.c568_pos (not_le.mp h693).le h0 (not_le.mp h867).le h866
    · -- right
      by_cases h868 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B028.c574_pos (not_le.mp h693).le h0 (not_le.mp h866).le h868
      · -- right
        exact CKLaneC2R.Cells.S00.B028.c576_pos (not_le.mp h693).le h0 (not_le.mp h868).le h861

theorem strip0_s079 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : ¬ (a ≤ ((11/64 : ℚ) : ℝ))) (h794 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h845 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h861 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h869 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h870 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h871 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B032.c642_pos (not_le.mp h693).le h0 (not_le.mp h861).le h871
    · -- right
      exact CKLaneC2R.Cells.S00.B032.c644_pos (not_le.mp h693).le h0 (not_le.mp h871).le h870
  · -- right
    by_cases h872 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      by_cases h873 : z ≤ ((117829/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B048.c975_pos (not_le.mp h693).le h0 (not_le.mp h870).le h873
      · -- right
        exact CKLaneC2R.Cells.S00.B048.c976_pos (not_le.mp h693).le h0 (not_le.mp h873).le h872
    · -- right
      by_cases h874 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B048.c979_pos (not_le.mp h693).le h0 (not_le.mp h872).le h874
      · -- right
        exact CKLaneC2R.Cells.S00.B049.c980_pos (not_le.mp h693).le h0 (not_le.mp h874).le h869

end CKLaneC2R.CompactCover


