-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g23
-- name    : CK_CKLaneC2R_CompactCover_S05_g23
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T02:02:43.808304+00:00
-- url     : https://prove2.me/theorems/016800d8-f5d1-45d9-a39b-c9fbe4999648
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
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B003
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B007

namespace CKLaneC2R.CompactCover

theorem strip5_s041 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : a ≤ ((7893/8000 : ℚ) : ℝ)) (h272 : ¬ (a ≤ ((15687/16000 : ℚ) : ℝ))) (h316 : a ≤ ((31473/32000 : ℚ) : ℝ)) (h317 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h318 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h319 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h320 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B006.c132_pos (not_le.mp h272).le h316 hz1 h320
      · -- right
        exact CKLaneC2R.Cells.S05.B006.c134_pos (not_le.mp h272).le h316 (not_le.mp h320).le h319
    · -- right
      exact CKLaneC2R.Cells.S05.B003.c79_pos (not_le.mp h272).le h316 (not_le.mp h319).le h318
  · -- right
    by_cases h321 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B004.c83_pos (not_le.mp h272).le h316 (not_le.mp h318).le h321
    · -- right
      exact CKLaneC2R.Cells.S05.B004.c87_pos (not_le.mp h272).le h316 (not_le.mp h321).le h317

theorem strip5_s042 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : a ≤ ((7893/8000 : ℚ) : ℝ)) (h272 : ¬ (a ≤ ((15687/16000 : ℚ) : ℝ))) (h316 : a ≤ ((31473/32000 : ℚ) : ℝ)) (h317 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h322 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h323 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h324 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B007.c149_pos (not_le.mp h272).le h316 (not_le.mp h317).le h324
    · -- right
      exact CKLaneC2R.Cells.S05.B007.c151_pos (not_le.mp h272).le h316 (not_le.mp h324).le h323
  · -- right
    by_cases h325 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B007.c153_pos (not_le.mp h272).le h316 (not_le.mp h323).le h325
    · -- right
      exact CKLaneC2R.Cells.S05.B007.c155_pos (not_le.mp h272).le h316 (not_le.mp h325).le h322

end CKLaneC2R.CompactCover


