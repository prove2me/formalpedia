-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0278
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0278
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:36:56.26069+00:00
-- url     : https://prove2.me/theorems/e8409e74-7e4d-4603-aa75-0e36ca931ab3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0278` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0278` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0278` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0278 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0278.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0278_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0278

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact2231 : RatBall := localContactBall tau2231 center2231
def work2231 : RoundedTauEval :=
  evalTau precision tau2231 contact2231 logTwoBall

theorem center_sq2231 : (center2231.re : ℝ)^2 +
    (center2231.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2231]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2231 : work2231.theta.ok = true ∧
    work2231.jac.invOK = true ∧ acceptsUnitSq work2231.out = true := by decide +kernel

def cell2231 : CellCertificate where
  tauBall := tau2231
  contactCenter := center2231
  contactBall := contact2231
  work := work2231
  center_sq := center_sq2231
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2231.1
  jac_ok := checks2231.2.1
  accepted := checks2231.2.2

def cells : List CellCertificate := [cell2224, cell2225, cell2226, cell2227, cell2228, cell2229, cell2230, cell2231]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0278


