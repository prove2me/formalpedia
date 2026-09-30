-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0110
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0110
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:26:32.692992+00:00
-- url     : https://prove2.me/theorems/e0b5c7b0-49f6-4bf8-bfe7-6e750c6c8476
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0110.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0110_part02

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact0887 : RatBall := localContactBall tau0887 center0887
def work0887 : RoundedTauEval :=
  evalTau precision tau0887 contact0887 logTwoBall

theorem center_sq0887 : (center0887.re : ℝ)^2 +
    (center0887.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0887]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0887 : work0887.theta.ok = true ∧
    work0887.jac.invOK = true ∧ acceptsUnitSq work0887.out = true := by decide +kernel

def cell0887 : CellCertificate where
  tauBall := tau0887
  contactCenter := center0887
  contactBall := contact0887
  work := work0887
  center_sq := center_sq0887
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0887.1
  jac_ok := checks0887.2.1
  accepted := checks0887.2.2

def cells : List CellCertificate := [cell0880, cell0881, cell0882, cell0883, cell0884, cell0885, cell0886, cell0887]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110


