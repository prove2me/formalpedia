-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0139
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0139
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:34:42.27091+00:00
-- url     : https://prove2.me/theorems/4262e70e-f5a1-494d-b6b8-1b254e82f028
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0139.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0139_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1119 : RoundedTauEval :=
  evalTau precision tau1119 contact1119 logTwoBall

theorem center_sq1119 : (center1119.re : ℝ)^2 +
    (center1119.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1119]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1119 : work1119.theta.ok = true ∧
    work1119.jac.invOK = true ∧ acceptsUnitSq work1119.out = true := by decide +kernel

def cell1119 : CellCertificate where
  tauBall := tau1119
  contactCenter := center1119
  contactBall := contact1119
  work := work1119
  center_sq := center_sq1119
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1119.1
  jac_ok := checks1119.2.1
  accepted := checks1119.2.2

def cells : List CellCertificate := [cell1112, cell1113, cell1114, cell1115, cell1116, cell1117, cell1118, cell1119]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139


