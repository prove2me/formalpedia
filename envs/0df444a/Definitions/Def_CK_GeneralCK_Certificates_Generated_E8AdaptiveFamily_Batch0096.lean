-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0096
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0096
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:35:42.814348+00:00
-- url     : https://prove2.me/theorems/4d5d611f-7760-452f-a158-6e73e33a7352
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0096.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0096_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work0775 : RoundedTauEval :=
  evalTau precision tau0775 contact0775 logTwoBall

theorem center_sq0775 : (center0775.re : ℝ)^2 +
    (center0775.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0775]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0775 : work0775.theta.ok = true ∧
    work0775.jac.invOK = true ∧ acceptsUnitSq work0775.out = true := by decide +kernel

def cell0775 : CellCertificate where
  tauBall := tau0775
  contactCenter := center0775
  contactBall := contact0775
  work := work0775
  center_sq := center_sq0775
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0775.1
  jac_ok := checks0775.2.1
  accepted := checks0775.2.2

def cells : List CellCertificate := [cell0768, cell0769, cell0770, cell0771, cell0772, cell0773, cell0774, cell0775]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096


