-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_SmallMeanCoverage
-- name    : CK_GeneralCK_Certificates_SmallMeanCoverage
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:29:36.970984+00:00
-- url     : https://prove2.me/theorems/722d9706-83b9-44f2-9e46-66759ea6ce59
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.SmallMeanCoverage` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.SmallMeanCoverage` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.SmallMeanCoverage` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.SmallMeanCoverage (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/SmallMeanCoverage.lean)

import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanLeaves

namespace GeneralCK.Certificates.SmallMean

theorem scalar_certificate (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (1/6 : ℝ) ≤ r) (hu : r ≤ 1) :
    0 < W gamma r := by
  by_cases hm : r ≤ (139 / 384)
  · have hu := hm
    by_cases hm : r ≤ (19 / 64)
    · have hu := hm
      by_cases hm : r ≤ (47 / 192)
      · have hu := hm
        by_cases hm : r ≤ (7 / 32)
        · have hu := hm
          exact leaf_0 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          exact leaf_1 gamma hmono heq r hl (by simpa only [div_one] using hu)
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : r ≤ (13 / 48)
        · have hu := hm
          exact leaf_2 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : r ≤ (109 / 384)
          · have hu := hm
            exact leaf_3 gamma hmono heq r hl (by simpa only [div_one] using hu)
          · have hl := (lt_of_not_ge hm).le
            exact leaf_4 gamma hmono heq r hl (by simpa only [div_one] using hu)
    · have hl := (lt_of_not_ge hm).le
      by_cases hm : r ≤ (31 / 96)
      · have hu := hm
        by_cases hm : r ≤ (119 / 384)
        · have hu := hm
          exact leaf_5 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          exact leaf_6 gamma hmono heq r hl (by simpa only [div_one] using hu)
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : r ≤ (43 / 128)
        · have hu := hm
          exact leaf_7 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : r ≤ (67 / 192)
          · have hu := hm
            exact leaf_8 gamma hmono heq r hl (by simpa only [div_one] using hu)
          · have hl := (lt_of_not_ge hm).le
            exact leaf_9 gamma hmono heq r hl (by simpa only [div_one] using hu)
  · have hl := (lt_of_not_ge hm).le
    by_cases hm : r ≤ (23 / 48)
    · have hu := hm
      by_cases hm : r ≤ (77 / 192)
      · have hu := hm
        by_cases hm : r ≤ (3 / 8)
        · have hu := hm
          exact leaf_10 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          exact leaf_11 gamma hmono heq r hl (by simpa only [div_one] using hu)
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : r ≤ (41 / 96)
        · have hu := hm
          exact leaf_12 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : r ≤ (29 / 64)
          · have hu := hm
            exact leaf_13 gamma hmono heq r hl (by simpa only [div_one] using hu)
          · have hl := (lt_of_not_ge hm).le
            exact leaf_14 gamma hmono heq r hl (by simpa only [div_one] using hu)
    · have hl := (lt_of_not_ge hm).le
      by_cases hm : r ≤ (7 / 12)
      · have hu := hm
        by_cases hm : r ≤ (17 / 32)
        · have hu := hm
          exact leaf_15 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          exact leaf_16 gamma hmono heq r hl (by simpa only [div_one] using hu)
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : r ≤ (11 / 16)
        · have hu := hm
          exact leaf_17 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : r ≤ (19 / 24)
          · have hu := hm
            exact leaf_18 gamma hmono heq r hl (by simpa only [div_one] using hu)
          · have hl := (lt_of_not_ge hm).le
            exact leaf_19 gamma hmono heq r hl (by simpa only [div_one] using hu)

end GeneralCK.Certificates.SmallMean


