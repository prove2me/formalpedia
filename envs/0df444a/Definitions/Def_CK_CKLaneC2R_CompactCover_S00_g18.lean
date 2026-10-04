-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g18
-- name    : CK_CKLaneC2R_CompactCover_S00_g18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T15:57:10.681205+00:00
-- url     : https://prove2.me/theorems/c7993d55-8c78-4a03-a7f0-73e93378d087
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B025
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B046
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B047

namespace CKLaneC2R.CompactCover

theorem strip0_s022 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((49/320 : ℚ) : ℝ))) (h133 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h202 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h218 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h219 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h220 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h221 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B025.c519_pos (not_le.mp h3).le h2 (not_le.mp h202).le h221
      · -- right
        exact CKLaneC2R.Cells.S00.B026.c520_pos (not_le.mp h3).le h2 (not_le.mp h221).le h220
    · -- right
      by_cases h222 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B026.c523_pos (not_le.mp h3).le h2 (not_le.mp h220).le h222
      · -- right
        exact CKLaneC2R.Cells.S00.B026.c524_pos (not_le.mp h3).le h2 (not_le.mp h222).le h219
  · -- right
    by_cases h223 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h224 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B027.c550_pos (not_le.mp h3).le h2 (not_le.mp h219).le h224
      · -- right
        exact CKLaneC2R.Cells.S00.B027.c551_pos (not_le.mp h3).le h2 (not_le.mp h224).le h223
    · -- right
      by_cases h225 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B027.c556_pos (not_le.mp h3).le h2 (not_le.mp h223).le h225
      · -- right
        by_cases h226 : z ≤ ((112351/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B046.c927_pos (not_le.mp h3).le h2 (not_le.mp h225).le h226
        · -- right
          exact CKLaneC2R.Cells.S00.B046.c928_pos (not_le.mp h3).le h2 (not_le.mp h226).le h218

theorem strip0_s023 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((49/320 : ℚ) : ℝ))) (h133 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h202 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h218 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h227 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h228 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h229 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      by_cases h230 : z ≤ ((114177/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B046.c931_pos (not_le.mp h3).le h2 (not_le.mp h218).le h230
      · -- right
        exact CKLaneC2R.Cells.S00.B046.c932_pos (not_le.mp h3).le h2 (not_le.mp h230).le h229
    · -- right
      by_cases h231 : z ≤ ((116003/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B046.c935_pos (not_le.mp h3).le h2 (not_le.mp h229).le h231
      · -- right
        exact CKLaneC2R.Cells.S00.B046.c936_pos (not_le.mp h3).le h2 (not_le.mp h231).le h228
  · -- right
    by_cases h232 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      by_cases h233 : z ≤ ((117829/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B047.c947_pos (not_le.mp h3).le h2 (not_le.mp h228).le h233
      · -- right
        exact CKLaneC2R.Cells.S00.B047.c948_pos (not_le.mp h3).le h2 (not_le.mp h233).le h232
    · -- right
      by_cases h234 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B047.c951_pos (not_le.mp h3).le h2 (not_le.mp h232).le h234
      · -- right
        exact CKLaneC2R.Cells.S00.B047.c952_pos (not_le.mp h3).le h2 (not_le.mp h234).le h227

end CKLaneC2R.CompactCover


