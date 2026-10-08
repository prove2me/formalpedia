-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionRemainingRegionsExtended_q00
-- name    : CK_GeneralCK_ReflectionRemainingRegionsExtended_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T10:21:04.805074+00:00
-- url     : https://prove2.me/theorems/527bb2ee-4f35-49b1-89f5-d97c4b2061ef
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionRemainingRegionsExtended (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionRemainingRegionsExtended (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionRemainingRegionsExtended (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionRemainingRegionsExtended (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionRemainingRegionsExtended (piece 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_ReflectionRemainingRegions
import Definitions.Def_CK_GeneralCK_ReflectionRemainingRegionsExtended_q00_mid



namespace GeneralCK.Reflection
open Set

/-- The two midpoint families, the completed boundary strip, and the
independent high-bias theorem cover every positive ratio through `1/20` for
all biases at least `3/20`. -/
theorem curvature_low_ratio_to_twentieth {a z : ℝ}
    (ha : (3/20:ℝ) ≤ a) (ha1 : a < 1) (hz : 0 < z) (hz1 : z ≤ 1/20) :
    0 < curvature a (a*z) := by
  by_cases hhigh : (999/1000:ℝ) ≤ a
  · apply curvature_high_bias hhigh ha1
    · exact mul_pos (by linarith) hz
    · nlinarith
  have habox : Certificates.Reflection.Bounds (3/20:ℝ) (999/1000) a :=
    ⟨ha, (lt_of_not_ge hhigh).le⟩
  by_cases hboundary : z ≤ (1/1000:ℝ)
  · exact curvature_low_ratio_large_bias ha ha1 hz hboundary
  exact curvature_midpoint_strips_to_twentieth habox (lt_of_not_ge hboundary) hz1

end GeneralCK.Reflection


