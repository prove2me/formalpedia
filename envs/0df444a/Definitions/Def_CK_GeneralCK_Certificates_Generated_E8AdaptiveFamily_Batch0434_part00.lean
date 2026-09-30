-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0434_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0434_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:58:47.614121+00:00
-- url     : https://prove2.me/theorems/56fab3ee-4a1c-4af8-8cf3-0a14ce886f1e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0434 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3472 : RatBall :=
  ⟨⟨-27/640, 253/640⟩, 3/1280⟩
def center3472 : GaussianRat :=
  ⟨-6970453/200000000, 289742037/1000000000⟩
def contact3472 : RatBall := localContactBall tau3472 center3472
def work3472 : RoundedTauEval :=
  evalTau precision tau3472 contact3472 logTwoBall

theorem center_sq3472 : (center3472.re : ℝ)^2 +
    (center3472.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3472]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3472 : work3472.theta.ok = true ∧
    work3472.jac.invOK = true ∧ acceptsUnitSq work3472.out = true := by decide +kernel

def cell3472 : CellCertificate where
  tauBall := tau3472
  contactCenter := center3472
  contactBall := contact3472
  work := work3472
  center_sq := center_sq3472
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3472.1
  jac_ok := checks3472.2.1
  accepted := checks3472.2.2

def tau3473 : RatBall :=
  ⟨⟨-5/128, 253/640⟩, 3/1280⟩
def center3473 : GaussianRat :=
  ⟨-16138267/500000000, 7246099/25000000⟩
def contact3473 : RatBall := localContactBall tau3473 center3473
def work3473 : RoundedTauEval :=
  evalTau precision tau3473 contact3473 logTwoBall

theorem center_sq3473 : (center3473.re : ℝ)^2 +
    (center3473.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3473]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3473 : work3473.theta.ok = true ∧
    work3473.jac.invOK = true ∧ acceptsUnitSq work3473.out = true := by decide +kernel

def cell3473 : CellCertificate where
  tauBall := tau3473
  contactCenter := center3473
  contactBall := contact3473
  work := work3473
  center_sq := center_sq3473
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3473.1
  jac_ok := checks3473.2.1
  accepted := checks3473.2.2

def tau3474 : RatBall :=
  ⟨⟨-27/640, 51/128⟩, 3/1280⟩
def center3474 : GaussianRat :=
  ⟨-34958801/1000000000, 14616047/50000000⟩
def contact3474 : RatBall := localContactBall tau3474 center3474
def work3474 : RoundedTauEval :=
  evalTau precision tau3474 contact3474 logTwoBall

theorem center_sq3474 : (center3474.re : ℝ)^2 +
    (center3474.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3474]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3474 : work3474.theta.ok = true ∧
    work3474.jac.invOK = true ∧ acceptsUnitSq work3474.out = true := by decide +kernel

def cell3474 : CellCertificate where
  tauBall := tau3474
  contactCenter := center3474
  contactBall := contact3474
  work := work3474
  center_sq := center_sq3474
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3474.1
  jac_ok := checks3474.2.1
  accepted := checks3474.2.2

def tau3475 : RatBall :=
  ⟨⟨-5/128, 51/128⟩, 3/1280⟩
def center3475 : GaussianRat :=
  ⟨-32375263/1000000000, 292424289/1000000000⟩
def contact3475 : RatBall := localContactBall tau3475 center3475
def work3475 : RoundedTauEval :=
  evalTau precision tau3475 contact3475 logTwoBall

theorem center_sq3475 : (center3475.re : ℝ)^2 +
    (center3475.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3475]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3475 : work3475.theta.ok = true ∧
    work3475.jac.invOK = true ∧ acceptsUnitSq work3475.out = true := by decide +kernel

def cell3475 : CellCertificate where
  tauBall := tau3475
  contactCenter := center3475
  contactBall := contact3475
  work := work3475
  center_sq := center_sq3475
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3475.1
  jac_ok := checks3475.2.1
  accepted := checks3475.2.2

def tau3476 : RatBall :=
  ⟨⟨-23/640, 249/640⟩, 3/1280⟩
def center3476 : GaussianRat :=
  ⟨-29521383/1000000000, 142399033/500000000⟩
def contact3476 : RatBall := localContactBall tau3476 center3476
def work3476 : RoundedTauEval :=
  evalTau precision tau3476 contact3476 logTwoBall

theorem center_sq3476 : (center3476.re : ℝ)^2 +
    (center3476.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3476]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3476 : work3476.theta.ok = true ∧
    work3476.jac.invOK = true ∧ acceptsUnitSq work3476.out = true := by decide +kernel

def cell3476 : CellCertificate where
  tauBall := tau3476
  contactCenter := center3476
  contactBall := contact3476
  work := work3476
  center_sq := center_sq3476
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3476.1
  jac_ok := checks3476.2.1
  accepted := checks3476.2.2

def tau3477 : RatBall :=
  ⟨⟨-21/640, 249/640⟩, 3/1280⟩
def center3477 : GaussianRat :=
  ⟨-26958403/1000000000, 284882077/1000000000⟩
def contact3477 : RatBall := localContactBall tau3477 center3477
def work3477 : RoundedTauEval :=
  evalTau precision tau3477 contact3477 logTwoBall

theorem center_sq3477 : (center3477.re : ℝ)^2 +
    (center3477.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3477]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434


