-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactAssembly
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactAssembly
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:37:03.476756+00:00
-- url     : https://prove2.me/theorems/73312873-393e-489a-9317-c5bfc361d3c1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactAssembly` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactAssembly` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginSourceKExactAssembly` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactAssembly (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactAssembly.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactExtensional

-- ===== source module GeneralCK.Certificates.E8OriginSourceKExactAssembly =====
section

namespace GeneralCK.Certificates.E8OriginSourceKExactAssembly

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKProducts
open E8OriginSourceAffineReplay
open E8OriginRealTaylorTransfer
open E8OriginSourceKExactReplay
open E8OriginSourceKCoefficientReplay

noncomputable def sourceK (s t : Real) : Real :=
  -4 * qSourceTaylorDerivative 0 s * qSourceTaylorDerivative 3 (2 * s + t) +
  qSourceTaylorDerivative 0 t * qSourceTaylorDerivative 3 (s + t) -
  8 * qSourceTaylorDerivative 0 t * qSourceTaylorDerivative 3 (2 * s + t) +
  4 * qSourceTaylorDerivative 0 (s + t) * qSourceTaylorDerivative 3 (2 * s + t) +
  qSourceTaylorDerivative 0 (2 * s + t) * qSourceTaylorDerivative 3 (s + t) -
  4 * qSourceTaylorDerivative 1 s * qSourceTaylorDerivative 2 (2 * s + t) +
  qSourceTaylorDerivative 2 s * qSourceTaylorDerivative 1 t -
  qSourceTaylorDerivative 2 s * qSourceTaylorDerivative 1 (2 * s + t) +
  qSourceTaylorDerivative 1 t * qSourceTaylorDerivative 2 (s + t) -
  8 * qSourceTaylorDerivative 1 t * qSourceTaylorDerivative 2 (2 * s + t) +
  8 * qSourceTaylorDerivative 1 (s + t) * qSourceTaylorDerivative 2 (2 * s + t) +
  5 * qSourceTaylorDerivative 2 (s + t) * qSourceTaylorDerivative 1 (2 * s + t)

theorem sourceK_eq_productData (s t : Real) :
    sourceK s t = evalTerms productData s t := by
  unfold sourceK productData
  simp only [evalTerms_append]
  rw [p0_eval, p1_eval, p2_eval, p3_eval, p4_eval, p5_eval,
    p6_eval, p7_eval, p8_eval, p9_eval, p10_eval, p11_eval]
  rw [← q0_1_0_eval, ← q3_2_1_eval, ← q0_0_1_eval,
    ← q3_1_1_eval, ← q0_1_1_eval, ← q0_2_1_eval,
    ← q1_1_0_eval, ← q2_2_1_eval, ← q2_1_0_eval,
    ← q1_0_1_eval, ← q1_2_1_eval, ← q2_1_1_eval,
    ← q1_1_1_eval]
  ring

theorem sourceK_eq_kData (s t : Real) :
    sourceK s t = evalTerms kData s t := by
  rw [sourceK_eq_productData, productData_eval_eq_kData]

end GeneralCK.Certificates.E8OriginSourceKExactAssembly

end


