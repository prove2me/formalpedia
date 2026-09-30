-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0449
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0449
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:23:10.893434+00:00
-- url     : https://prove2.me/theorems/36386d4c-a655-4b3c-a15e-889711a224c6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0449.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0449_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3597 : RoundedTauEval :=
  evalTau precision tau3597 contact3597 logTwoBall

theorem center_sq3597 : (center3597.re : ℝ)^2 +
    (center3597.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3597]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3597 : work3597.theta.ok = true ∧
    work3597.jac.invOK = true ∧ acceptsUnitSq work3597.out = true := by decide +kernel

def cell3597 : CellCertificate where
  tauBall := tau3597
  contactCenter := center3597
  contactBall := contact3597
  work := work3597
  center_sq := center_sq3597
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3597.1
  jac_ok := checks3597.2.1
  accepted := checks3597.2.2

def tau3598 : RatBall :=
  ⟨⟨29/640, 51/128⟩, 3/1280⟩
def center3598 : GaussianRat :=
  ⟨2346303/62500000, 292209741/1000000000⟩
def contact3598 : RatBall := localContactBall tau3598 center3598
def work3598 : RoundedTauEval :=
  evalTau precision tau3598 contact3598 logTwoBall

theorem center_sq3598 : (center3598.re : ℝ)^2 +
    (center3598.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3598]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3598 : work3598.theta.ok = true ∧
    work3598.jac.invOK = true ∧ acceptsUnitSq work3598.out = true := by decide +kernel

def cell3598 : CellCertificate where
  tauBall := tau3598
  contactCenter := center3598
  contactBall := contact3598
  work := work3598
  center_sq := center_sq3598
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3598.1
  jac_ok := checks3598.2.1
  accepted := checks3598.2.2

def tau3599 : RatBall :=
  ⟨⟨31/640, 51/128⟩, 3/1280⟩
def center3599 : GaussianRat :=
  ⟨20060649/500000000, 146045357/500000000⟩
def contact3599 : RatBall := localContactBall tau3599 center3599
def work3599 : RoundedTauEval :=
  evalTau precision tau3599 contact3599 logTwoBall

theorem center_sq3599 : (center3599.re : ℝ)^2 +
    (center3599.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3599]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3599 : work3599.theta.ok = true ∧
    work3599.jac.invOK = true ∧ acceptsUnitSq work3599.out = true := by decide +kernel

def cell3599 : CellCertificate where
  tauBall := tau3599
  contactCenter := center3599
  contactBall := contact3599
  work := work3599
  center_sq := center_sq3599
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3599.1
  jac_ok := checks3599.2.1
  accepted := checks3599.2.2

def cells : List CellCertificate := [cell3592, cell3593, cell3594, cell3595, cell3596, cell3597, cell3598, cell3599]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449


