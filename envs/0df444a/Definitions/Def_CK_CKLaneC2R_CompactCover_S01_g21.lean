-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g21
-- name    : CK_CKLaneC2R_CompactCover_S01_g21
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T05:11:17.938119+00:00
-- url     : https://prove2.me/theorems/a51fc4b2-4d7d-4030-b38d-e2d5f50cf0c3
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B013

namespace CKLaneC2R.CompactCover

theorem strip1_s027 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : a ≤ ((7/32 : ℚ) : ℝ)) (h225 : z ≤ ((217/400 : ℚ) : ℝ)) (h226 : ¬ (a ≤ ((69/320 : ℚ) : ℝ))) (h254 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h273 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h274 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h275 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B011.c223_pos (not_le.mp h226).le h224 (not_le.mp h254).le h275
      · -- right
        exact CKLaneC2R.Cells.S01.B011.c225_pos (not_le.mp h226).le h224 (not_le.mp h275).le h274
    · -- right
      by_cases h276 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B011.c231_pos (not_le.mp h226).le h224 (not_le.mp h274).le h276
      · -- right
        exact CKLaneC2R.Cells.S01.B011.c233_pos (not_le.mp h226).le h224 (not_le.mp h276).le h273
  · -- right
    by_cases h277 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h278 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B012.c255_pos (not_le.mp h226).le h224 (not_le.mp h273).le h278
      · -- right
        exact CKLaneC2R.Cells.S01.B012.c257_pos (not_le.mp h226).le h224 (not_le.mp h278).le h277
    · -- right
      by_cases h279 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B013.c263_pos (not_le.mp h226).le h224 (not_le.mp h277).le h279
      · -- right
        exact CKLaneC2R.Cells.S01.B013.c265_pos (not_le.mp h226).le h224 (not_le.mp h279).le h225

end CKLaneC2R.CompactCover


