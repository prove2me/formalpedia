-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g22
-- name    : CK_CKLaneC2R_CompactCover_S02_g22
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T05:25:51.926978+00:00
-- url     : https://prove2.me/theorems/f6b14968-3726-4431-8978-cab8c4141985
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S02 (proof part of strip2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S02 (proof part of strip2).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B019

namespace CKLaneC2R.CompactCover

theorem strip2_s034 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : a ≤ ((3/8 : ℚ) : ℝ)) (h316 : ¬ (a ≤ ((29/80 : ℚ) : ℝ))) (h375 : z ≤ ((217/400 : ℚ) : ℝ)) (h376 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h377 : a ≤ ((59/160 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h378 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h379 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h380 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h381 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B031.c639_pos (not_le.mp h316).le h377 hz1 h381
        · -- right
          exact CKLaneC2R.Cells.S02.B032.c641_pos (not_le.mp h316).le h377 (not_le.mp h381).le h380
      · -- right
        by_cases h382 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B032.c647_pos (not_le.mp h316).le h377 (not_le.mp h380).le h382
        · -- right
          exact CKLaneC2R.Cells.S02.B032.c649_pos (not_le.mp h316).le h377 (not_le.mp h382).le h379
    · -- right
      by_cases h383 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h384 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B033.c671_pos (not_le.mp h316).le h377 (not_le.mp h379).le h384
        · -- right
          exact CKLaneC2R.Cells.S02.B033.c673_pos (not_le.mp h316).le h377 (not_le.mp h384).le h383
      · -- right
        exact CKLaneC2R.Cells.S02.B018.c372_pos (not_le.mp h316).le h377 (not_le.mp h383).le h378
  · -- right
    by_cases h385 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h386 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B019.c385_pos (not_le.mp h316).le h377 (not_le.mp h378).le h386
      · -- right
        exact CKLaneC2R.Cells.S02.B019.c387_pos (not_le.mp h316).le h377 (not_le.mp h386).le h385
    · -- right
      by_cases h387 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B019.c393_pos (not_le.mp h316).le h377 (not_le.mp h385).le h387
      · -- right
        exact CKLaneC2R.Cells.S02.B019.c395_pos (not_le.mp h316).le h377 (not_le.mp h387).le h376

theorem strip2_s035 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : a ≤ ((3/8 : ℚ) : ℝ)) (h316 : ¬ (a ≤ ((29/80 : ℚ) : ℝ))) (h375 : z ≤ ((217/400 : ℚ) : ℝ)) (h376 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h377 : ¬ (a ≤ ((59/160 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h388 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h389 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h390 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h391 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B032.c640_pos (not_le.mp h377).le h315 hz1 h391
        · -- right
          exact CKLaneC2R.Cells.S02.B032.c642_pos (not_le.mp h377).le h315 (not_le.mp h391).le h390
      · -- right
        by_cases h392 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B032.c648_pos (not_le.mp h377).le h315 (not_le.mp h390).le h392
        · -- right
          exact CKLaneC2R.Cells.S02.B032.c650_pos (not_le.mp h377).le h315 (not_le.mp h392).le h389
    · -- right
      by_cases h393 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h394 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B033.c672_pos (not_le.mp h377).le h315 (not_le.mp h389).le h394
        · -- right
          exact CKLaneC2R.Cells.S02.B033.c674_pos (not_le.mp h377).le h315 (not_le.mp h394).le h393
      · -- right
        exact CKLaneC2R.Cells.S02.B018.c373_pos (not_le.mp h377).le h315 (not_le.mp h393).le h388
  · -- right
    by_cases h395 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h396 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B019.c386_pos (not_le.mp h377).le h315 (not_le.mp h388).le h396
      · -- right
        exact CKLaneC2R.Cells.S02.B019.c388_pos (not_le.mp h377).le h315 (not_le.mp h396).le h395
    · -- right
      by_cases h397 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B019.c394_pos (not_le.mp h377).le h315 (not_le.mp h395).le h397
      · -- right
        exact CKLaneC2R.Cells.S02.B019.c396_pos (not_le.mp h377).le h315 (not_le.mp h397).le h376

end CKLaneC2R.CompactCover


