-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0448
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0448
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:47:44.714698+00:00
-- url     : https://prove2.me/theorems/ba488c5f-78fd-4956-8e07-cfeec32afe6d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0448.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0448_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3591 : RoundedTauEval :=
  evalTau precision tau3591 contact3591 logTwoBall

theorem center_sq3591 : (center3591.re : ℝ)^2 +
    (center3591.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3591]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3591 : work3591.theta.ok = true ∧
    work3591.jac.invOK = true ∧ acceptsUnitSq work3591.out = true := by decide +kernel

def cell3591 : CellCertificate where
  tauBall := tau3591
  contactCenter := center3591
  contactBall := contact3591
  work := work3591
  center_sq := center_sq3591
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3591.1
  jac_ok := checks3591.2.1
  accepted := checks3591.2.2

def cells : List CellCertificate := [cell3584, cell3585, cell3586, cell3587, cell3588, cell3589, cell3590, cell3591]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448


