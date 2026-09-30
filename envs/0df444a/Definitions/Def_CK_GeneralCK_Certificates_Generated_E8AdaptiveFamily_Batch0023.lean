-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0023
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0023
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:44:17.350242+00:00
-- url     : https://prove2.me/theorems/5fbca9c5-faf1-4673-9d33-6a52639bf562
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0023.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0023_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work0191 : RoundedTauEval :=
  evalTau precision tau0191 contact0191 logTwoBall

theorem center_sq0191 : (center0191.re : ℝ)^2 +
    (center0191.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0191]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0191 : work0191.theta.ok = true ∧
    work0191.jac.invOK = true ∧ acceptsUnitSq work0191.out = true := by decide +kernel

def cell0191 : CellCertificate where
  tauBall := tau0191
  contactCenter := center0191
  contactBall := contact0191
  work := work0191
  center_sq := center_sq0191
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0191.1
  jac_ok := checks0191.2.1
  accepted := checks0191.2.2

def cells : List CellCertificate := [cell0184, cell0185, cell0186, cell0187, cell0188, cell0189, cell0190, cell0191]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023


