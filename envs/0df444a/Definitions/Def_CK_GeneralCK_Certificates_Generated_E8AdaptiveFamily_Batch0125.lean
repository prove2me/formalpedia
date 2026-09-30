-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0125
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0125
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:20:55.646196+00:00
-- url     : https://prove2.me/theorems/1718727f-10d3-41ef-a4a2-03bb1b2301d5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0125.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0125_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1007 : RoundedTauEval :=
  evalTau precision tau1007 contact1007 logTwoBall

theorem center_sq1007 : (center1007.re : ℝ)^2 +
    (center1007.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1007]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1007 : work1007.theta.ok = true ∧
    work1007.jac.invOK = true ∧ acceptsUnitSq work1007.out = true := by decide +kernel

def cell1007 : CellCertificate where
  tauBall := tau1007
  contactCenter := center1007
  contactBall := contact1007
  work := work1007
  center_sq := center_sq1007
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1007.1
  jac_ok := checks1007.2.1
  accepted := checks1007.2.2

def cells : List CellCertificate := [cell1000, cell1001, cell1002, cell1003, cell1004, cell1005, cell1006, cell1007]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125


