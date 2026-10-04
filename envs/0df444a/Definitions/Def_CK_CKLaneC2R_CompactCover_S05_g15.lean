-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g15
-- name    : CK_CKLaneC2R_CompactCover_S05_g15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T10:12:42.059542+00:00
-- url     : https://prove2.me/theorems/9abdf502-6a25-449d-8e9b-5b242f3593fc
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B003
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B009

namespace CKLaneC2R.CompactCover

theorem strip5_s023 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : ¬ (a ≤ ((1539/1600 : ℚ) : ℝ))) (h199 : a ≤ ((15489/16000 : ℚ) : ℝ)) (h200 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h201 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h202 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h203 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B003.c60_pos (not_le.mp h148).le h199 hz1 h203
      · -- right
        exact CKLaneC2R.Cells.S05.B003.c62_pos (not_le.mp h148).le h199 (not_le.mp h203).le h202
    · -- right
      by_cases h204 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B003.c64_pos (not_le.mp h148).le h199 (not_le.mp h202).le h204
      · -- right
        exact CKLaneC2R.Cells.S05.B003.c65_pos (not_le.mp h148).le h199 (not_le.mp h204).le h201
  · -- right
    by_cases h205 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h206 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B003.c68_pos (not_le.mp h148).le h199 (not_le.mp h201).le h206
      · -- right
        exact CKLaneC2R.Cells.S05.B003.c69_pos (not_le.mp h148).le h199 (not_le.mp h206).le h205
    · -- right
      by_cases h207 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B003.c72_pos (not_le.mp h148).le h199 (not_le.mp h205).le h207
      · -- right
        exact CKLaneC2R.Cells.S05.B003.c74_pos (not_le.mp h148).le h199 (not_le.mp h207).le h200

theorem strip5_s024 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : ¬ (a ≤ ((1539/1600 : ℚ) : ℝ))) (h199 : a ≤ ((15489/16000 : ℚ) : ℝ)) (h200 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h208 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h209 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h210 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B004.c99_pos (not_le.mp h148).le h199 (not_le.mp h200).le h210
    · -- right
      exact CKLaneC2R.Cells.S05.B005.c101_pos (not_le.mp h148).le h199 (not_le.mp h210).le h209
  · -- right
    by_cases h211 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B005.c105_pos (not_le.mp h148).le h199 (not_le.mp h209).le h211
    · -- right
      exact CKLaneC2R.Cells.S05.B005.c109_pos (not_le.mp h148).le h199 (not_le.mp h211).le h208

theorem strip5_s025 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : ¬ (a ≤ ((1539/1600 : ℚ) : ℝ))) (h199 : a ≤ ((15489/16000 : ℚ) : ℝ)) (h200 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h208 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h212 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h213 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h214 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B008.c170_pos (not_le.mp h148).le h199 (not_le.mp h208).le h214
    · -- right
      exact CKLaneC2R.Cells.S05.B008.c172_pos (not_le.mp h148).le h199 (not_le.mp h214).le h213
  · -- right
    by_cases h215 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B008.c178_pos (not_le.mp h148).le h199 (not_le.mp h213).le h215
    · -- right
      exact CKLaneC2R.Cells.S05.B009.c180_pos (not_le.mp h148).le h199 (not_le.mp h215).le h212

end CKLaneC2R.CompactCover


