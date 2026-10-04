-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g17
-- name    : CK_CKLaneC2R_CompactCover_S00_g17
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T14:52:55.63841+00:00
-- url     : https://prove2.me/theorems/61d7eeb5-54cd-4e59-9d66-1668869582b8
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B021

namespace CKLaneC2R.CompactCover

theorem strip0_s021 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((49/320 : ℚ) : ℝ))) (h133 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h202 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h203 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h204 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h205 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        by_cases h206 : z ≤ ((35633/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B017.c347_pos (not_le.mp h3).le h2 (not_le.mp h133).le h206
        · -- right
          exact CKLaneC2R.Cells.S00.B017.c348_pos (not_le.mp h3).le h2 (not_le.mp h206).le h205
      · -- right
        by_cases h207 : z ≤ ((37459/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B017.c351_pos (not_le.mp h3).le h2 (not_le.mp h205).le h207
        · -- right
          exact CKLaneC2R.Cells.S00.B017.c352_pos (not_le.mp h3).le h2 (not_le.mp h207).le h204
    · -- right
      by_cases h208 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        by_cases h209 : z ≤ ((7857/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B018.c363_pos (not_le.mp h3).le h2 (not_le.mp h204).le h209
        · -- right
          exact CKLaneC2R.Cells.S00.B018.c364_pos (not_le.mp h3).le h2 (not_le.mp h209).le h208
      · -- right
        by_cases h210 : z ≤ ((41111/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B018.c367_pos (not_le.mp h3).le h2 (not_le.mp h208).le h210
        · -- right
          exact CKLaneC2R.Cells.S00.B018.c368_pos (not_le.mp h3).le h2 (not_le.mp h210).le h203
  · -- right
    by_cases h211 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h212 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        by_cases h213 : z ≤ ((42937/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B020.c411_pos (not_le.mp h3).le h2 (not_le.mp h203).le h213
        · -- right
          exact CKLaneC2R.Cells.S00.B020.c412_pos (not_le.mp h3).le h2 (not_le.mp h213).le h212
      · -- right
        by_cases h214 : z ≤ ((44763/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B020.c415_pos (not_le.mp h3).le h2 (not_le.mp h212).le h214
        · -- right
          exact CKLaneC2R.Cells.S00.B020.c416_pos (not_le.mp h3).le h2 (not_le.mp h214).le h211
    · -- right
      by_cases h215 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h216 : z ≤ ((46589/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B021.c427_pos (not_le.mp h3).le h2 (not_le.mp h211).le h216
        · -- right
          exact CKLaneC2R.Cells.S00.B021.c428_pos (not_le.mp h3).le h2 (not_le.mp h216).le h215
      · -- right
        by_cases h217 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B021.c431_pos (not_le.mp h3).le h2 (not_le.mp h215).le h217
        · -- right
          exact CKLaneC2R.Cells.S00.B021.c432_pos (not_le.mp h3).le h2 (not_le.mp h217).le h202

end CKLaneC2R.CompactCover


