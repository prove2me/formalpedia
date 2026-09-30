-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0457
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0457
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:36:00.262426+00:00
-- url     : https://prove2.me/theorems/4efdbbc5-0165-4ad4-8917-e21bf5a927f3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0457` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0457` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0457` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0457 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0457.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0457_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0457

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact3662 : RatBall := localContactBall tau3662 center3662
def work3662 : RoundedTauEval :=
  evalTau precision tau3662 contact3662 logTwoBall

theorem center_sq3662 : (center3662.re : ℝ)^2 +
    (center3662.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3662]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3662 : work3662.theta.ok = true ∧
    work3662.jac.invOK = true ∧ acceptsUnitSq work3662.out = true := by decide +kernel

def cell3662 : CellCertificate where
  tauBall := tau3662
  contactCenter := center3662
  contactBall := contact3662
  work := work3662
  center_sq := center_sq3662
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3662.1
  jac_ok := checks3662.2.1
  accepted := checks3662.2.2

def tau3663 : RatBall :=
  ⟨⟨61/640, 241/640⟩, 3/1280⟩
def center3663 : GaussianRat :=
  ⟨38493039/500000000, 67940497/250000000⟩
def contact3663 : RatBall := localContactBall tau3663 center3663
def work3663 : RoundedTauEval :=
  evalTau precision tau3663 contact3663 logTwoBall

theorem center_sq3663 : (center3663.re : ℝ)^2 +
    (center3663.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3663]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3663 : work3663.theta.ok = true ∧
    work3663.jac.invOK = true ∧ acceptsUnitSq work3663.out = true := by decide +kernel

def cell3663 : CellCertificate where
  tauBall := tau3663
  contactCenter := center3663
  contactBall := contact3663
  work := work3663
  center_sq := center_sq3663
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3663.1
  jac_ok := checks3663.2.1
  accepted := checks3663.2.2

def cells : List CellCertificate := [cell3656, cell3657, cell3658, cell3659, cell3660, cell3661, cell3662, cell3663]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0457


