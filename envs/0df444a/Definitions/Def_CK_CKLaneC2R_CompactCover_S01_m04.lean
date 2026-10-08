-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_m04
-- name    : CK_CKLaneC2R_CompactCover_S01_m04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T18:23:11.229892+00:00
-- url     : https://prove2.me/theorems/95234fb3-78ef-40db-9f57-17d7511bc8b0
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g34
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g35
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g36
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g37
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g38
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g39
import Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g40

namespace CKLaneC2R.CompactCover

theorem strip1_m04 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : a ≤ ((37/160 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h421 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h422 : a ≤ ((73/320 : ℚ) : ℝ)
    · -- left
      by_cases h423 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h424 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s042 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h421 h422 h423 h424
        · -- right
          exact strip1_s043 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h421 h422 h423 h424
      · -- right
        exact strip1_s044 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h421 h422 h423
    · -- right
      by_cases h447 : z ≤ ((1257/4000 : ℚ) : ℝ)
      · -- left
        by_cases h448 : z ≤ ((1601/8000 : ℚ) : ℝ)
        · -- left
          exact strip1_s045 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h421 h422 h447 h448
        · -- right
          exact strip1_s046 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h421 h422 h447 h448
      · -- right
        exact strip1_s047 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h421 h422 h447
  · -- right
    by_cases h471 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip1_s048 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h421 h471
    · -- right
      by_cases h487 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip1_s049 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h421 h471 h487
      · -- right
        by_cases h495 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip1_s050 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h421 h471 h487 h495
        · -- right
          exact strip1_s051 ha1 ha2 hz1 hz2 h0 h1 h419 h420 h421 h471 h487 h495

end CKLaneC2R.CompactCover


