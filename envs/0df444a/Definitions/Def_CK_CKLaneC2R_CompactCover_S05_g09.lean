-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g09
-- name    : CK_CKLaneC2R_CompactCover_S05_g09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T20:33:02.804997+00:00
-- url     : https://prove2.me/theorems/3192a478-cb0e-486b-bcea-34e0b5e08334
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S05 (proof part of strip5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S05 (proof part of strip5).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B008

namespace CKLaneC2R.CompactCover

theorem strip5_s015 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((3699/4000 : ℚ) : ℝ))) (h69 : ¬ (a ≤ ((7497/8000 : ℚ) : ℝ))) (h107 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h116 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h121 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h122 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h123 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B006.c125_pos (not_le.mp h69).le h0 (not_le.mp h116).le h123
    · -- right
      exact CKLaneC2R.Cells.S05.B006.c126_pos (not_le.mp h69).le h0 (not_le.mp h123).le h122
  · -- right
    by_cases h124 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B006.c128_pos (not_le.mp h69).le h0 (not_le.mp h122).le h124
    · -- right
      by_cases h125 : a ≤ ((15093/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B008.c166_pos (not_le.mp h69).le h125 (not_le.mp h124).le h121
      · -- right
        exact CKLaneC2R.Cells.S05.B008.c167_pos (not_le.mp h125).le h0 (not_le.mp h124).le h121

end CKLaneC2R.CompactCover


