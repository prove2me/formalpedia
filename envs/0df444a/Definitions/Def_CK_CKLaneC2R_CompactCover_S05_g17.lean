-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g17
-- name    : CK_CKLaneC2R_CompactCover_S05_g17
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T18:52:08.972026+00:00
-- url     : https://prove2.me/theorems/25ffac3d-e74d-4a6b-a2b5-8da972af90fb
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B021
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B024
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B003
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B005

namespace CKLaneC2R.CompactCover

theorem strip5_s028 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : ¬ (a ≤ ((1539/1600 : ℚ) : ℝ))) (h199 : a ≤ ((15489/16000 : ℚ) : ℝ)) (h200 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h208 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h212 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h216 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h220 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h224 : a ≤ ((30879/32000 : ℚ) : ℝ)
  · -- left
    by_cases h225 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h226 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B021.c423_pos (not_le.mp h148).le h224 (not_le.mp h220).le h226
      · -- right
        exact CKLaneC2R.Cells.S05.B021.c425_pos (not_le.mp h148).le h224 (not_le.mp h226).le h225
    · -- right
      by_cases h227 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B021.c436_pos (not_le.mp h148).le h224 (not_le.mp h225).le h227
      · -- right
        by_cases h228 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B024.c495_pos (not_le.mp h148).le h224 (not_le.mp h227).le h228
        · -- right
          by_cases h229 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B026.c528_pos (not_le.mp h148).le h224 (not_le.mp h228).le h229
          · -- right
            exact CKLaneC2R.Cells.S05.B026.c529_pos (not_le.mp h148).le h224 (not_le.mp h229).le hz2
  · -- right
    by_cases h230 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h231 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B021.c424_pos (not_le.mp h224).le h199 (not_le.mp h220).le h231
      · -- right
        exact CKLaneC2R.Cells.S05.B021.c426_pos (not_le.mp h224).le h199 (not_le.mp h231).le h230
    · -- right
      by_cases h232 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B021.c437_pos (not_le.mp h224).le h199 (not_le.mp h230).le h232
      · -- right
        by_cases h233 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B024.c496_pos (not_le.mp h224).le h199 (not_le.mp h232).le h233
        · -- right
          by_cases h234 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B026.c530_pos (not_le.mp h224).le h199 (not_le.mp h233).le h234
          · -- right
            exact CKLaneC2R.Cells.S05.B026.c531_pos (not_le.mp h224).le h199 (not_le.mp h234).le hz2

theorem strip5_s029 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : ¬ (a ≤ ((1539/1600 : ℚ) : ℝ))) (h199 : ¬ (a ≤ ((15489/16000 : ℚ) : ℝ))) (h235 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h236 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h237 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h238 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B003.c61_pos (not_le.mp h199).le h147 hz1 h238
      · -- right
        exact CKLaneC2R.Cells.S05.B003.c63_pos (not_le.mp h199).le h147 (not_le.mp h238).le h237
    · -- right
      by_cases h239 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B003.c66_pos (not_le.mp h199).le h147 (not_le.mp h237).le h239
      · -- right
        exact CKLaneC2R.Cells.S05.B003.c67_pos (not_le.mp h199).le h147 (not_le.mp h239).le h236
  · -- right
    by_cases h240 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h241 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B003.c70_pos (not_le.mp h199).le h147 (not_le.mp h236).le h241
      · -- right
        exact CKLaneC2R.Cells.S05.B003.c71_pos (not_le.mp h199).le h147 (not_le.mp h241).le h240
    · -- right
      by_cases h242 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B003.c73_pos (not_le.mp h199).le h147 (not_le.mp h240).le h242
      · -- right
        exact CKLaneC2R.Cells.S05.B003.c75_pos (not_le.mp h199).le h147 (not_le.mp h242).le h235

theorem strip5_s030 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : ¬ (a ≤ ((1539/1600 : ℚ) : ℝ))) (h199 : ¬ (a ≤ ((15489/16000 : ℚ) : ℝ))) (h235 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h243 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h244 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h245 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B005.c100_pos (not_le.mp h199).le h147 (not_le.mp h235).le h245
    · -- right
      exact CKLaneC2R.Cells.S05.B005.c102_pos (not_le.mp h199).le h147 (not_le.mp h245).le h244
  · -- right
    by_cases h246 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B005.c106_pos (not_le.mp h199).le h147 (not_le.mp h244).le h246
    · -- right
      exact CKLaneC2R.Cells.S05.B005.c110_pos (not_le.mp h199).le h147 (not_le.mp h246).le h243

end CKLaneC2R.CompactCover


