-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g19
-- name    : CK_CKLaneC2R_CompactCover_S01_g19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T18:12:48.409876+00:00
-- url     : https://prove2.me/theorems/0bde101b-2080-4cff-85af-eda5b60fff3e
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B049
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B050
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B032

namespace CKLaneC2R.CompactCover

theorem strip1_s025 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : a ≤ ((7/32 : ℚ) : ℝ)) (h225 : z ≤ ((217/400 : ℚ) : ℝ)) (h226 : ¬ (a ≤ ((69/320 : ℚ) : ℝ))) (h254 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h255 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h256 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h257 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h258 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h259 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B049.c981_pos (not_le.mp h226).le h224 hz1 h259
        · -- right
          exact CKLaneC2R.Cells.S01.B049.c983_pos (not_le.mp h226).le h224 (not_le.mp h259).le h258
      · -- right
        by_cases h260 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B049.c986_pos (not_le.mp h226).le h224 (not_le.mp h258).le h260
        · -- right
          exact CKLaneC2R.Cells.S01.B049.c987_pos (not_le.mp h226).le h224 (not_le.mp h260).le h257
    · -- right
      by_cases h261 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h262 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B049.c998_pos (not_le.mp h226).le h224 (not_le.mp h257).le h262
        · -- right
          exact CKLaneC2R.Cells.S01.B049.c999_pos (not_le.mp h226).le h224 (not_le.mp h262).le h261
      · -- right
        by_cases h263 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B050.c1002_pos (not_le.mp h226).le h224 (not_le.mp h261).le h263
        · -- right
          exact CKLaneC2R.Cells.S01.B050.c1003_pos (not_le.mp h226).le h224 (not_le.mp h263).le h256
  · -- right
    by_cases h264 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h265 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B032.c648_pos (not_le.mp h226).le h224 (not_le.mp h256).le h265
      · -- right
        exact CKLaneC2R.Cells.S01.B032.c650_pos (not_le.mp h226).le h224 (not_le.mp h265).le h264
    · -- right
      by_cases h266 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B032.c656_pos (not_le.mp h226).le h224 (not_le.mp h264).le h266
      · -- right
        exact CKLaneC2R.Cells.S01.B032.c658_pos (not_le.mp h226).le h224 (not_le.mp h266).le h255

end CKLaneC2R.CompactCover


