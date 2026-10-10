-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionRemainingRegionsCertified
-- name    : CK_GeneralCK_ReflectionRemainingRegionsCertified
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T18:48:56.059471+00:00
-- url     : https://prove2.me/theorems/21f7909d-46a6-4f18-890e-f12a5a2dfe38
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionRemainingRegionsCertified` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionRemainingRegionsCertified` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionRemainingRegionsCertified` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionRemainingRegionsCertified (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionRemainingRegionsCertified.lean)

import Definitions.Def_CK_GeneralCK_ReflectionRemainingRegionsCertified_q01

namespace GeneralCK.Reflection
open Set
/-- Every completed reflection certificate family, including the
post-next-band family, covers all positive ratios through `43 / 500`.

This is the current reduction boundary for the global curvature obligation:
only small bias `a ≤ 3 / 20` and the compact rectangle with ratio strictly
above `43 / 500` remain. -/
theorem curvature_nonneg_of_remaining_regions_post_next_band
    (hsmall : ∀ a b : ℝ, 0 < b → b < a → a ≤ 3 / 20 → 0 ≤ curvature a b)
    (hcompact : ∀ a z : ℝ, a ∈ Icc (3 / 20 : ℝ) (999 / 1000) →
      z ∈ Ioo (43 / 500 : ℝ) 1 → 0 ≤ curvature a (a * z))
    {a b : ℝ} (hb : 0 < b) (hba : b < a) (ha1 : a < 1) :
    0 ≤ curvature a b := by
  by_cases hsmall_a : a ≤ (3 / 20 : ℝ)
  · exact hsmall a b hb hba hsmall_a
  have ha : (3 / 20 : ℝ) ≤ a := (lt_of_not_ge hsmall_a).le
  have ha0 : 0 < a := hb.trans hba
  have hab : a * (b / a) = b := by field_simp
  have hz : 0 < b / a := div_pos hb ha0
  have hz1 : b / a < 1 := (div_lt_one ha0).mpr hba
  by_cases hhigh : (999 / 1000 : ℝ) ≤ a
  · exact (curvature_high_bias hhigh ha1 hb hba).le
  have habox : Certificates.Reflection.Bounds
      (3 / 20 : ℝ) (999 / 1000) a := ⟨ha, (lt_of_not_ge hhigh).le⟩
  by_cases hcovered : b / a ≤ (43 / 500 : ℝ)
  · simpa only [hab] using
      (GeneralCK.Certificates.ReflectionMidpointCombinedCoverage.full_positive_ratio_through_post_next_band
        habox ⟨hz, hcovered⟩).le
  · simpa only [hab] using hcompact a (b / a) habox
      ⟨lt_of_not_ge hcovered, hz1⟩

#print axioms curvature_nonneg_of_remaining_regions_post_next_band

end GeneralCK.Reflection


