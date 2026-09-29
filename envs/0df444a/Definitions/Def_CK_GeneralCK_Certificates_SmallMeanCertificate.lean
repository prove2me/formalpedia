-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_SmallMeanCertificate
-- name    : CK_GeneralCK_Certificates_SmallMeanCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:33:50.307984+00:00
-- url     : https://prove2.me/theorems/b2578ccf-07d8-43cf-aba7-adfca4d40541
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.SmallMeanCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.SmallMeanCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.SmallMeanCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.SmallMeanCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/SmallMeanCertificate.lean)

import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanCoverage
import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanFixed
import Definitions.Def_CK_GeneralCK_SmallMeanAnalytic

namespace GeneralCK.Certificates.SmallMean

/-- All twenty original closed intervals, with the analytic monotonicity discharged. -/
theorem small_mean_scalar (r : ℝ) (hl : (1/6 : ℝ) ≤ r) (hu : r ≤ 1) :
    0 < (1862/2883)*r^2-(23/10)*(201/1000)+
      GeneralCK.SmallMean.gamma r*((201/1000)-(1/31)*r^2) :=
  scalar_certificate GeneralCK.SmallMean.gamma GeneralCK.SmallMean.gamma_antitone rfl r hl hu

theorem fixed_gamma_sixth : (23/10 : ℝ) < GeneralCK.SmallMean.gamma (1/6) := gamma_sixth_gt

theorem fixed_log_two_lt : Real.log 2 < (7/10 : ℝ) := by
  have h := PilotData.log_two.2
  norm_num only [div_one] at h
  linarith only [h]

theorem fixed_small_ratio_positive : (0 : ℝ) < 1862/2883-(14/5)*(1/31) := by norm_num

end GeneralCK.Certificates.SmallMean


