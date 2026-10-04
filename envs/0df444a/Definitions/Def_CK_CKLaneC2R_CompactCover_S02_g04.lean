-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g04
-- name    : CK_CKLaneC2R_CompactCover_S02_g04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T20:19:31.690415+00:00
-- url     : https://prove2.me/theorems/bebc0cfd-95bb-4805-ad1d-cd318336c52a
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B024
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B025
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B035

namespace CKLaneC2R.CompactCover

theorem strip2_s005 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : a ≤ ((5/16 : ℚ) : ℝ)) (h4 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h50 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h66 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h67 : a ≤ ((49/160 : ℚ) : ℝ)
  · -- left
    by_cases h68 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h69 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B024.c489_pos ha1 h67 (not_le.mp h50).le h69
      · -- right
        exact CKLaneC2R.Cells.S02.B024.c491_pos ha1 h67 (not_le.mp h69).le h68
    · -- right
      by_cases h70 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B024.c497_pos ha1 h67 (not_le.mp h68).le h70
      · -- right
        exact CKLaneC2R.Cells.S02.B024.c499_pos ha1 h67 (not_le.mp h70).le h66
  · -- right
    by_cases h71 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h72 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B024.c490_pos (not_le.mp h67).le h3 (not_le.mp h50).le h72
      · -- right
        exact CKLaneC2R.Cells.S02.B024.c492_pos (not_le.mp h67).le h3 (not_le.mp h72).le h71
    · -- right
      by_cases h73 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B024.c498_pos (not_le.mp h67).le h3 (not_le.mp h71).le h73
      · -- right
        exact CKLaneC2R.Cells.S02.B025.c500_pos (not_le.mp h67).le h3 (not_le.mp h73).le h66

theorem strip2_s006 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : a ≤ ((5/16 : ℚ) : ℝ)) (h4 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h50 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h66 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h74 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h75 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h76 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B025.c519_pos ha1 h3 (not_le.mp h66).le h76
    · -- right
      exact CKLaneC2R.Cells.S02.B026.c520_pos ha1 h3 (not_le.mp h76).le h75
  · -- right
    by_cases h77 : a ≤ ((49/160 : ℚ) : ℝ)
    · -- left
      by_cases h78 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B034.c697_pos ha1 h77 (not_le.mp h75).le h78
      · -- right
        exact CKLaneC2R.Cells.S02.B034.c699_pos ha1 h77 (not_le.mp h78).le h74
    · -- right
      by_cases h79 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B034.c698_pos (not_le.mp h77).le h3 (not_le.mp h75).le h79
      · -- right
        exact CKLaneC2R.Cells.S02.B035.c700_pos (not_le.mp h77).le h3 (not_le.mp h79).le h74

end CKLaneC2R.CompactCover


