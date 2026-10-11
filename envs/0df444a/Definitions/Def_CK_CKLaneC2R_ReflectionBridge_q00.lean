-- Prove2me | Definitions.Def_CK_CKLaneC2R_ReflectionBridge_q00
-- name    : CK_CKLaneC2R_ReflectionBridge_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-11T10:28:33.195804+00:00
-- url     : https://prove2.me/theorems/2f6c514b-0d61-4445-aa5c-4bf834f4934b
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.ReflectionBridge (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.ReflectionBridge (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.ReflectionBridge (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.ReflectionBridge (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/ReflectionBridge (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneC2R_HCompact
import Definitions.Def_CK_GeneralCK_ReflectionSmallBias
import Definitions.Def_CK_GeneralCK_ReflectionRemainingRegionsCertified



/-!
# Lane C2: the reflection field at its exact type

`GeneralCK.Reflection.curvature_nonneg_of_remaining_regions_post_next_band` (F-C root) reduces the
reflection curvature inequality to
* `hsmall` — supplied by `GeneralCK.Reflection.curvature_nonneg_small_bias`
  (module `GeneralCK.ReflectionSmallBias`; the 113-module small-bias chain from
  `~/gck_lanes/P-REFL/work/farm_insitu`, whose whole import closure is byte-identical to this
  provider apart from those 113 modules — see C2/LOG.md 03:24Z), and
* `hcompact` — `CKLaneC2R.hcompact_certified` (5,079 compact + 2,922 endpoint reflective cells).
-/

namespace CKLaneC2R

/-- The consumer with the certified compact input; conditional only on `hsmall`. -/
theorem reflection_of_hsmall
    (hsmall : ∀ a b : ℝ, 0 < b → b < a → a ≤ 3 / 20 → 0 ≤ GeneralCK.Reflection.curvature a b) :
    ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ GeneralCK.Reflection.curvature a b :=
  fun _ _ hb hba ha =>
    GeneralCK.Reflection.curvature_nonneg_of_remaining_regions_post_next_band hsmall
      hcompact_certified hb hba ha

end CKLaneC2R


