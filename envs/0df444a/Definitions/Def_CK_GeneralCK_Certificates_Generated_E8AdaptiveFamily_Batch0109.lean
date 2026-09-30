-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0109
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0109
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:29:49.444621+00:00
-- url     : https://prove2.me/theorems/53ee3008-c734-447e-aaaf-514accb25da1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0109.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0109_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work0879 : RoundedTauEval :=
  evalTau precision tau0879 contact0879 logTwoBall

theorem center_sq0879 : (center0879.re : ℝ)^2 +
    (center0879.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0879]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0879 : work0879.theta.ok = true ∧
    work0879.jac.invOK = true ∧ acceptsUnitSq work0879.out = true := by decide +kernel

def cell0879 : CellCertificate where
  tauBall := tau0879
  contactCenter := center0879
  contactBall := contact0879
  work := work0879
  center_sq := center_sq0879
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0879.1
  jac_ok := checks0879.2.1
  accepted := checks0879.2.2

def cells : List CellCertificate := [cell0872, cell0873, cell0874, cell0875, cell0876, cell0877, cell0878, cell0879]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109


