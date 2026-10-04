-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g17
-- name    : CK_CKLaneC2R_CompactCover_S01_g17
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T11:28:20.207275+00:00
-- url     : https://prove2.me/theorems/28718794-47f1-4ae3-8bfe-d5b1d97851d7
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
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B035

namespace CKLaneC2R.CompactCover

theorem strip1_s022 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : a ≤ ((7/32 : ℚ) : ℝ)) (h225 : z ≤ ((217/400 : ℚ) : ℝ)) (h226 : a ≤ ((69/320 : ℚ) : ℝ)) (h227 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h228 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h229 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h230 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h231 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h232 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B049.c980_pos (not_le.mp h2).le h226 hz1 h232
        · -- right
          exact CKLaneC2R.Cells.S01.B049.c982_pos (not_le.mp h2).le h226 (not_le.mp h232).le h231
      · -- right
        by_cases h233 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B049.c984_pos (not_le.mp h2).le h226 (not_le.mp h231).le h233
        · -- right
          exact CKLaneC2R.Cells.S01.B049.c985_pos (not_le.mp h2).le h226 (not_le.mp h233).le h230
    · -- right
      by_cases h234 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h235 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B049.c996_pos (not_le.mp h2).le h226 (not_le.mp h230).le h235
        · -- right
          exact CKLaneC2R.Cells.S01.B049.c997_pos (not_le.mp h2).le h226 (not_le.mp h235).le h234
      · -- right
        by_cases h236 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B050.c1000_pos (not_le.mp h2).le h226 (not_le.mp h234).le h236
        · -- right
          exact CKLaneC2R.Cells.S01.B050.c1001_pos (not_le.mp h2).le h226 (not_le.mp h236).le h229
  · -- right
    by_cases h237 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h238 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B032.c647_pos (not_le.mp h2).le h226 (not_le.mp h229).le h238
      · -- right
        exact CKLaneC2R.Cells.S01.B032.c649_pos (not_le.mp h2).le h226 (not_le.mp h238).le h237
    · -- right
      by_cases h239 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B032.c655_pos (not_le.mp h2).le h226 (not_le.mp h237).le h239
      · -- right
        exact CKLaneC2R.Cells.S01.B032.c657_pos (not_le.mp h2).le h226 (not_le.mp h239).le h228

theorem strip1_s023 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : a ≤ ((7/32 : ℚ) : ℝ)) (h225 : z ≤ ((217/400 : ℚ) : ℝ)) (h226 : a ≤ ((69/320 : ℚ) : ℝ)) (h227 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h228 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h240 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h241 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h242 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B034.c695_pos (not_le.mp h2).le h226 (not_le.mp h228).le h242
      · -- right
        exact CKLaneC2R.Cells.S01.B034.c697_pos (not_le.mp h2).le h226 (not_le.mp h242).le h241
    · -- right
      by_cases h243 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B035.c703_pos (not_le.mp h2).le h226 (not_le.mp h241).le h243
      · -- right
        exact CKLaneC2R.Cells.S01.B035.c704_pos (not_le.mp h2).le h226 (not_le.mp h243).le h240
  · -- right
    by_cases h244 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h245 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B035.c711_pos (not_le.mp h2).le h226 (not_le.mp h240).le h245
      · -- right
        exact CKLaneC2R.Cells.S01.B035.c712_pos (not_le.mp h2).le h226 (not_le.mp h245).le h244
    · -- right
      by_cases h246 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B035.c715_pos (not_le.mp h2).le h226 (not_le.mp h244).le h246
      · -- right
        exact CKLaneC2R.Cells.S01.B035.c716_pos (not_le.mp h2).le h226 (not_le.mp h246).le h227

end CKLaneC2R.CompactCover


