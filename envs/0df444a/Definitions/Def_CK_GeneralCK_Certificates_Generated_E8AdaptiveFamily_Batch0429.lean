-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0429
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0429
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:27:10.319846+00:00
-- url     : https://prove2.me/theorems/4a8ed8e9-1ca1-449d-b47e-7ea96a617480
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0429.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0429_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3436 : (center3436.re : ℝ)^2 +
    (center3436.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3436]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3436 : work3436.theta.ok = true ∧
    work3436.jac.invOK = true ∧ acceptsUnitSq work3436.out = true := by decide +kernel

def cell3436 : CellCertificate where
  tauBall := tau3436
  contactCenter := center3436
  contactBall := contact3436
  work := work3436
  center_sq := center_sq3436
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3436.1
  jac_ok := checks3436.2.1
  accepted := checks3436.2.2

def tau3437 : RatBall :=
  ⟨⟨-37/640, 249/640⟩, 3/1280⟩
def center3437 : GaussianRat :=
  ⟨-11855567/250000000, 283999143/1000000000⟩
def contact3437 : RatBall := localContactBall tau3437 center3437
def work3437 : RoundedTauEval :=
  evalTau precision tau3437 contact3437 logTwoBall

theorem center_sq3437 : (center3437.re : ℝ)^2 +
    (center3437.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3437]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3437 : work3437.theta.ok = true ∧
    work3437.jac.invOK = true ∧ acceptsUnitSq work3437.out = true := by decide +kernel

def cell3437 : CellCertificate where
  tauBall := tau3437
  contactCenter := center3437
  contactBall := contact3437
  work := work3437
  center_sq := center_sq3437
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3437.1
  jac_ok := checks3437.2.1
  accepted := checks3437.2.2

def tau3438 : RatBall :=
  ⟨⟨-39/640, 251/640⟩, 3/1280⟩
def center3438 : GaussianRat :=
  ⟨-10024261/200000000, 14320409/50000000⟩
def contact3438 : RatBall := localContactBall tau3438 center3438
def work3438 : RoundedTauEval :=
  evalTau precision tau3438 contact3438 logTwoBall

theorem center_sq3438 : (center3438.re : ℝ)^2 +
    (center3438.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3438]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3438 : work3438.theta.ok = true ∧
    work3438.jac.invOK = true ∧ acceptsUnitSq work3438.out = true := by decide +kernel

def cell3438 : CellCertificate where
  tauBall := tau3438
  contactCenter := center3438
  contactBall := contact3438
  work := work3438
  center_sq := center_sq3438
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3438.1
  jac_ok := checks3438.2.1
  accepted := checks3438.2.2

def tau3439 : RatBall :=
  ⟨⟨-37/640, 251/640⟩, 3/1280⟩
def center3439 : GaussianRat :=
  ⟨-4756353/100000000, 4477409/15625000⟩
def contact3439 : RatBall := localContactBall tau3439 center3439
def work3439 : RoundedTauEval :=
  evalTau precision tau3439 contact3439 logTwoBall

theorem center_sq3439 : (center3439.re : ℝ)^2 +
    (center3439.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3439]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3439 : work3439.theta.ok = true ∧
    work3439.jac.invOK = true ∧ acceptsUnitSq work3439.out = true := by decide +kernel

def cell3439 : CellCertificate where
  tauBall := tau3439
  contactCenter := center3439
  contactBall := contact3439
  work := work3439
  center_sq := center_sq3439
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3439.1
  jac_ok := checks3439.2.1
  accepted := checks3439.2.2

def cells : List CellCertificate := [cell3432, cell3433, cell3434, cell3435, cell3436, cell3437, cell3438, cell3439]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429


