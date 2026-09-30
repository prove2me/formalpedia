-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0164
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0164
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:22:22.901146+00:00
-- url     : https://prove2.me/theorems/1ba8ae15-049c-47d0-80a0-10a8ac6474c8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0164.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0164_part02

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact1319 : RatBall := localContactBall tau1319 center1319
def work1319 : RoundedTauEval :=
  evalTau precision tau1319 contact1319 logTwoBall

theorem center_sq1319 : (center1319.re : ℝ)^2 +
    (center1319.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1319]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1319 : work1319.theta.ok = true ∧
    work1319.jac.invOK = true ∧ acceptsUnitSq work1319.out = true := by decide +kernel

def cell1319 : CellCertificate where
  tauBall := tau1319
  contactCenter := center1319
  contactBall := contact1319
  work := work1319
  center_sq := center_sq1319
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1319.1
  jac_ok := checks1319.2.1
  accepted := checks1319.2.2

def cells : List CellCertificate := [cell1312, cell1313, cell1314, cell1315, cell1316, cell1317, cell1318, cell1319]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164


