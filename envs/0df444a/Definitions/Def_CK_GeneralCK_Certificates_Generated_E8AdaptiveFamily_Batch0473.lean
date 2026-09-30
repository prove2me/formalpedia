-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0473
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0473
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:15:28.496723+00:00
-- url     : https://prove2.me/theorems/24396c46-293b-4806-b98e-4497e10f0662
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0473.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0473_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center3790 : GaussianRat :=
  ⟨67704553/500000000, 6135977/25000000⟩
def contact3790 : RatBall := localContactBall tau3790 center3790
def work3790 : RoundedTauEval :=
  evalTau precision tau3790 contact3790 logTwoBall

theorem center_sq3790 : (center3790.re : ℝ)^2 +
    (center3790.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3790]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3790 : work3790.theta.ok = true ∧
    work3790.jac.invOK = true ∧ acceptsUnitSq work3790.out = true := by decide +kernel

def cell3790 : CellCertificate where
  tauBall := tau3790
  contactCenter := center3790
  contactBall := contact3790
  work := work3790
  center_sq := center_sq3790
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3790.1
  jac_ok := checks3790.2.1
  accepted := checks3790.2.2

def tau3791 : RatBall :=
  ⟨⟨109/640, 227/640⟩, 3/1280⟩
def center3791 : GaussianRat :=
  ⟨133380131/1000000000, 248126483/1000000000⟩
def contact3791 : RatBall := localContactBall tau3791 center3791
def work3791 : RoundedTauEval :=
  evalTau precision tau3791 contact3791 logTwoBall

theorem center_sq3791 : (center3791.re : ℝ)^2 +
    (center3791.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3791]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3791 : work3791.theta.ok = true ∧
    work3791.jac.invOK = true ∧ acceptsUnitSq work3791.out = true := by decide +kernel

def cell3791 : CellCertificate where
  tauBall := tau3791
  contactCenter := center3791
  contactBall := contact3791
  work := work3791
  center_sq := center_sq3791
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3791.1
  jac_ok := checks3791.2.1
  accepted := checks3791.2.2

def cells : List CellCertificate := [cell3784, cell3785, cell3786, cell3787, cell3788, cell3789, cell3790, cell3791]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473


