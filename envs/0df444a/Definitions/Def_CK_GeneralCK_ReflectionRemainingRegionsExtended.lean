-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionRemainingRegionsExtended
-- name    : CK_GeneralCK_ReflectionRemainingRegionsExtended
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T19:40:43.454596+00:00
-- url     : https://prove2.me/theorems/9f185241-9b83-4515-8e46-3b8fd23ce4a1
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionRemainingRegionsExtended` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionRemainingRegionsExtended` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionRemainingRegionsExtended` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionRemainingRegionsExtended (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionRemainingRegionsExtended.lean)

import Definitions.Def_CK_GeneralCK_ReflectionRemainingRegionsExtended_q00

namespace GeneralCK.Reflection
open Set
/-- After the two midpoint families, the compact reflection premise starts
strictly above `z=1/20`; all lower ratios and endpoint overlaps are proved. -/
theorem curvature_nonneg_of_remaining_regions_extended
    (hsmall : ∀ a b : ℝ, 0 < b → b < a → a ≤ 3/20 → 0 ≤ curvature a b)
    (hcompact : ∀ a z : ℝ, a ∈ Icc (3/20:ℝ) (999/1000) →
      z ∈ Ioo (1/20:ℝ) 1 → 0 ≤ curvature a (a*z))
    {a b : ℝ} (hb : 0 < b) (hba : b < a) (ha1 : a < 1) :
    0 ≤ curvature a b := by
  refine curvature_nonneg_of_remaining_regions hsmall ?_ hb hba ha1
  intro x z hx hz
  by_cases hlow : z ≤ (1/20:ℝ)
  · exact (curvature_low_ratio_to_twentieth hx.1 (hx.2.trans_lt (by norm_num))
      (by linarith [hz.1]) hlow).le
  · exact hcompact x z hx ⟨lt_of_not_ge hlow, hz.2⟩

end GeneralCK.Reflection


