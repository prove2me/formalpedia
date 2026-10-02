-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKResidualLower_q02
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKResidualLower_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:06:41.431239+00:00
-- url     : https://prove2.me/theorems/01006350-3bec-43c5-82e0-2646f9755fa9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKResidualLower (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginSourceKResidualLower (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginSourceKResidualLower (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKResidualLower (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKResidualLower (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKResidualLower_q01

namespace GeneralCK.Certificates.E8OriginSourceKResidualLower
open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKCoefficientReplay
open E8OriginSourceKExactAssembly
open E8OriginRemainder
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000 in
theorem aggregate_eval :
    (6 / 100000 : Real) +
      negAggregate (2 / 25 : Real) (negativePart residualData) =
        (aggregate : Real) := by
  norm_num [negAggregate, negativePart, residualData, aggregate]

theorem aggregate_gt : (599 / 10000000 : Real) < (aggregate : Real) := by
  norm_num [aggregate]

theorem sourceK_lower {s t : Real} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hR : s + t ≤ (2 / 25 : Real)) :
    (599 / 10000000 : Real) * (s + t) ^ 3 ≤ sourceK s t := by
  rw [sourceK_eq_kData]
  have hp := evalTerms_nonneg (xs := nonnegativePart residualData) hs ht
    (coefficientsNonnegative_sound residual_nonnegative_coefficients)
  have hn := evalTerms_lower_negAggregate
    (xs := negativePart residualData) hs ht hR
    (degreesAtLeastThree_sound residual_degrees)
    (coefficientsNonpositive_sound residual_negative_coefficients)
  have hres :
      negAggregate (2 / 25 : Real) (negativePart residualData) *
          (s + t) ^ 3 ≤ evalTerms residualData s t := by
    rw [evalTerms_parts residualData]
    linarith
  rw [residual_eval] at hres
  have hagg := aggregate_gt
  rw [← aggregate_eval] at hagg
  nlinarith [pow_nonneg (add_nonneg hs ht) 3]

end GeneralCK.Certificates.E8OriginSourceKResidualLower


