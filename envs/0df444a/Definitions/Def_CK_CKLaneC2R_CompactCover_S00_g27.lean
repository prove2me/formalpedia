-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g27
-- name    : CK_CKLaneC2R_CompactCover_S00_g27
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T18:38:37.163904+00:00
-- url     : https://prove2.me/theorems/8d675470-3c97-4093-acbb-c2155231491e
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B046
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B047

namespace CKLaneC2R.CompactCover

theorem strip0_s032 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : a ≤ ((51/320 : ℚ) : ℝ)) (h254 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h319 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h335 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h336 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h337 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h338 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B026.c525_pos (not_le.mp h2).le h253 (not_le.mp h319).le h338
      · -- right
        exact CKLaneC2R.Cells.S00.B026.c526_pos (not_le.mp h2).le h253 (not_le.mp h338).le h337
    · -- right
      by_cases h339 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B026.c529_pos (not_le.mp h2).le h253 (not_le.mp h337).le h339
      · -- right
        exact CKLaneC2R.Cells.S00.B026.c530_pos (not_le.mp h2).le h253 (not_le.mp h339).le h336
  · -- right
    by_cases h340 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h341 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B027.c552_pos (not_le.mp h2).le h253 (not_le.mp h336).le h341
      · -- right
        exact CKLaneC2R.Cells.S00.B027.c553_pos (not_le.mp h2).le h253 (not_le.mp h341).le h340
    · -- right
      by_cases h342 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B027.c557_pos (not_le.mp h2).le h253 (not_le.mp h340).le h342
      · -- right
        exact CKLaneC2R.Cells.S00.B027.c559_pos (not_le.mp h2).le h253 (not_le.mp h342).le h335

theorem strip0_s033 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : a ≤ ((51/320 : ℚ) : ℝ)) (h254 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h319 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h335 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h343 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h344 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h345 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      by_cases h346 : z ≤ ((114177/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B046.c937_pos (not_le.mp h2).le h253 (not_le.mp h335).le h346
      · -- right
        exact CKLaneC2R.Cells.S00.B046.c938_pos (not_le.mp h2).le h253 (not_le.mp h346).le h345
    · -- right
      by_cases h347 : z ≤ ((116003/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B047.c941_pos (not_le.mp h2).le h253 (not_le.mp h345).le h347
      · -- right
        exact CKLaneC2R.Cells.S00.B047.c942_pos (not_le.mp h2).le h253 (not_le.mp h347).le h344
  · -- right
    by_cases h348 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      by_cases h349 : z ≤ ((117829/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B047.c953_pos (not_le.mp h2).le h253 (not_le.mp h344).le h349
      · -- right
        exact CKLaneC2R.Cells.S00.B047.c954_pos (not_le.mp h2).le h253 (not_le.mp h349).le h348
    · -- right
      by_cases h350 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B047.c957_pos (not_le.mp h2).le h253 (not_le.mp h348).le h350
      · -- right
        exact CKLaneC2R.Cells.S00.B047.c958_pos (not_le.mp h2).le h253 (not_le.mp h350).le h343

end CKLaneC2R.CompactCover


