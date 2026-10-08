-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_m04
-- name    : CK_CKLaneC2R_CompactCover_S00_m04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T18:51:38.211058+00:00
-- url     : https://prove2.me/theorems/fb3905bc-7043-4cc0-8a30-c5a447351150
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g39
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g40
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g41
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g42
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g43
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g44
import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g45

namespace CKLaneC2R.CompactCover

theorem strip0_m04 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : a ≤ ((53/320 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h483 : z ≤ ((217/400 : ℚ) : ℝ)
  · -- left
    by_cases h484 : z ≤ ((1257/4000 : ℚ) : ℝ)
    · -- left
      by_cases h485 : z ≤ ((1601/8000 : ℚ) : ℝ)
      · -- left
        by_cases h486 : a ≤ ((21/128 : ℚ) : ℝ)
        · -- left
          exact strip0_s046 ha1 ha2 hz1 hz2 h0 h1 h481 h482 h483 h484 h485 h486
        · -- right
          exact strip0_s047 ha1 ha2 hz1 hz2 h0 h1 h481 h482 h483 h484 h485 h486
      · -- right
        exact strip0_s048 ha1 ha2 hz1 hz2 h0 h1 h481 h482 h483 h484 h485
    · -- right
      exact strip0_s049 ha1 ha2 hz1 hz2 h0 h1 h481 h482 h483 h484
  · -- right
    by_cases h542 : z ≤ ((3083/4000 : ℚ) : ℝ)
    · -- left
      exact strip0_s050 ha1 ha2 hz1 hz2 h0 h1 h481 h482 h483 h542
    · -- right
      by_cases h558 : z ≤ ((7079/8000 : ℚ) : ℝ)
      · -- left
        exact strip0_s051 ha1 ha2 hz1 hz2 h0 h1 h481 h482 h483 h542 h558
      · -- right
        by_cases h566 : z ≤ ((15071/16000 : ℚ) : ℝ)
        · -- left
          exact strip0_s052 ha1 ha2 hz1 hz2 h0 h1 h481 h482 h483 h542 h558 h566
        · -- right
          by_cases h573 : z ≤ ((6211/6400 : ℚ) : ℝ)
          · -- left
            exact strip0_s053 ha1 ha2 hz1 hz2 h0 h1 h481 h482 h483 h542 h558 h566 h573
          · -- right
            exact strip0_s054 ha1 ha2 hz1 hz2 h0 h1 h481 h482 h483 h542 h558 h566 h573

end CKLaneC2R.CompactCover


