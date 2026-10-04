-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_All
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_All
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T14:38:33.824502+00:00
-- url     : https://prove2.me/theorems/ec8ea6a2-a425-401e-9653-af1175ee9a1d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.All` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.All` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.All` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.All (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddleAggregation/All.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddleAggregation_Part000__8

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.All =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem doubleCapLowMiddleAggregation : ∀ m : ℝ, 1 / 100 ≤ m → m ≤ 1 / 5 →
    0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  by_cases hp000 : m ≤ (2523 / 204800 : ℝ)
  · exact Part000.cover m (by linarith [hmLo]) hp000
  ·
    by_cases hp001 : m ≤ (3131 / 204800 : ℝ)
    · exact Part001.cover m (by linarith [(lt_of_not_ge hp000).le]) hp001
    ·
      by_cases hp002 : m ≤ (1063 / 51200 : ℝ)
      · exact Part002.cover m (by linarith [(lt_of_not_ge hp001).le]) hp002
      ·
        by_cases hp003 : m ≤ (1519 / 51200 : ℝ)
        · exact Part003.cover m (by linarith [(lt_of_not_ge hp002).le]) hp003
        ·
          by_cases hp004 : m ≤ (1187 / 25600 : ℝ)
          · exact Part004.cover m (by linarith [(lt_of_not_ge hp003).le]) hp004
          ·
            by_cases hp005 : m ≤ (1059 / 12800 : ℝ)
            · exact Part005.cover m (by linarith [(lt_of_not_ge hp004).le]) hp005
            ·
              by_cases hp006 : m ≤ (141 / 800 : ℝ)
              · exact Part006.cover m (by linarith [(lt_of_not_ge hp005).le]) hp006
              ·
                exact Part007.cover m (by linarith [(lt_of_not_ge hp006).le]) hmHi

#print axioms doubleCapLowMiddleAggregation
end GeneralCK.Certificates.DoubleCapLowMiddleAggregation

end


