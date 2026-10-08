-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m02
-- name    : CK_CKLaneC2R_CompactCover_S01_m02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T20:22:51.214997+00:00
-- url     : https://prove2.me/theorems/4989a415-300a-4fba-ac9d-57156031c736
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g17
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g18
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g19
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g20
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g21
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g22
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g23
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g24

namespace CKLaneC2R.CompactCover

theorem strip1_m02 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : a ≤ ((7/32 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h225 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h226 : a ≤ ((69/320 : ℚ) : ℝ)
    · -- left
      by_cases h227 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h228 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s022 ha1 ha2 hz1 hz2 h0 h1 h2 h224 h225 h226 h227 h228
        · -- right
          exact strip1_s023 ha1 ha2 hz1 hz2 h0 h1 h2 h224 h225 h226 h227 h228
      · -- right
        exact strip1_s024 ha1 ha2 hz1 hz2 h0 h1 h2 h224 h225 h226 h227
    · -- right
      by_cases h254 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h255 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s025 ha1 ha2 hz1 hz2 h0 h1 h2 h224 h225 h226 h254 h255
        · -- right
          exact strip1_s026 ha1 ha2 hz1 hz2 h0 h1 h2 h224 h225 h226 h254 h255
      · -- right
        exact strip1_s027 ha1 ha2 hz1 hz2 h0 h1 h2 h224 h225 h226 h254
  · -- right
    by_cases h280 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip1_s028 ha1 ha2 hz1 hz2 h0 h1 h2 h224 h225 h280
    · -- right
      by_cases h296 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip1_s029 ha1 ha2 hz1 hz2 h0 h1 h2 h224 h225 h280 h296
      · -- right
        by_cases h304 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip1_s030 ha1 ha2 hz1 hz2 h0 h1 h2 h224 h225 h280 h296 h304
        · -- right
          exact strip1_s031 ha1 ha2 hz1 hz2 h0 h1 h2 h224 h225 h280 h296 h304

end CKLaneC2R.CompactCover


