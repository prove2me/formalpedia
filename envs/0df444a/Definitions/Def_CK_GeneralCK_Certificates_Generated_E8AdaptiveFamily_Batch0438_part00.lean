-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0438_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0438_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:17:17.478663+00:00
-- url     : https://prove2.me/theorems/00e49d60-a12e-4af0-97d0-4c502432b410
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0438 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3504 : RatBall :=
  ⟨⟨-11/640, 253/640⟩, 3/1280⟩
def center3504 : GaussianRat :=
  ⟨-7107163/500000000, 290339131/1000000000⟩
def contact3504 : RatBall := localContactBall tau3504 center3504
def work3504 : RoundedTauEval :=
  evalTau precision tau3504 contact3504 logTwoBall

theorem center_sq3504 : (center3504.re : ℝ)^2 +
    (center3504.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3504]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3504 : work3504.theta.ok = true ∧
    work3504.jac.invOK = true ∧ acceptsUnitSq work3504.out = true := by decide +kernel

def cell3504 : CellCertificate where
  tauBall := tau3504
  contactCenter := center3504
  contactBall := contact3504
  work := work3504
  center_sq := center_sq3504
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3504.1
  jac_ok := checks3504.2.1
  accepted := checks3504.2.2

def tau3505 : RatBall :=
  ⟨⟨-9/640, 253/640⟩, 3/1280⟩
def center3505 : GaussianRat :=
  ⟨-5815363/500000000, 145189259/500000000⟩
def contact3505 : RatBall := localContactBall tau3505 center3505
def work3505 : RoundedTauEval :=
  evalTau precision tau3505 contact3505 logTwoBall

theorem center_sq3505 : (center3505.re : ℝ)^2 +
    (center3505.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3505]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3505 : work3505.theta.ok = true ∧
    work3505.jac.invOK = true ∧ acceptsUnitSq work3505.out = true := by decide +kernel

def cell3505 : CellCertificate where
  tauBall := tau3505
  contactCenter := center3505
  contactBall := contact3505
  work := work3505
  center_sq := center_sq3505
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3505.1
  jac_ok := checks3505.2.1
  accepted := checks3505.2.2

def tau3506 : RatBall :=
  ⟨⟨-11/640, 51/128⟩, 3/1280⟩
def center3506 : GaussianRat :=
  ⟨-3564487/250000000, 73231599/250000000⟩
def contact3506 : RatBall := localContactBall tau3506 center3506
def work3506 : RoundedTauEval :=
  evalTau precision tau3506 contact3506 logTwoBall

theorem center_sq3506 : (center3506.re : ℝ)^2 +
    (center3506.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3506]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3506 : work3506.theta.ok = true ∧
    work3506.jac.invOK = true ∧ acceptsUnitSq work3506.out = true := by decide +kernel

def cell3506 : CellCertificate where
  tauBall := tau3506
  contactCenter := center3506
  contactBall := contact3506
  work := work3506
  center_sq := center_sq3506
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3506.1
  jac_ok := checks3506.2.1
  accepted := checks3506.2.2

def tau3507 : RatBall :=
  ⟨⟨-9/640, 51/128⟩, 3/1280⟩
def center3507 : GaussianRat :=
  ⟨-11666429/1000000000, 4577599/15625000⟩
def contact3507 : RatBall := localContactBall tau3507 center3507
def work3507 : RoundedTauEval :=
  evalTau precision tau3507 contact3507 logTwoBall

theorem center_sq3507 : (center3507.re : ℝ)^2 +
    (center3507.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3507]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3507 : work3507.theta.ok = true ∧
    work3507.jac.invOK = true ∧ acceptsUnitSq work3507.out = true := by decide +kernel

def cell3507 : CellCertificate where
  tauBall := tau3507
  contactCenter := center3507
  contactBall := contact3507
  work := work3507
  center_sq := center_sq3507
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3507.1
  jac_ok := checks3507.2.1
  accepted := checks3507.2.2

def tau3508 : RatBall :=
  ⟨⟨-7/640, 249/640⟩, 3/1280⟩
def center3508 : GaussianRat :=
  ⟨-2248057/250000000, 142628517/500000000⟩
def contact3508 : RatBall := localContactBall tau3508 center3508
def work3508 : RoundedTauEval :=
  evalTau precision tau3508 contact3508 logTwoBall

theorem center_sq3508 : (center3508.re : ℝ)^2 +
    (center3508.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3508]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3508 : work3508.theta.ok = true ∧
    work3508.jac.invOK = true ∧ acceptsUnitSq work3508.out = true := by decide +kernel

def cell3508 : CellCertificate where
  tauBall := tau3508
  contactCenter := center3508
  contactBall := contact3508
  work := work3508
  center_sq := center_sq3508
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3508.1
  jac_ok := checks3508.2.1
  accepted := checks3508.2.2

def tau3509 : RatBall :=
  ⟨⟨-1/128, 249/640⟩, 3/1280⟩
def center3509 : GaussianRat :=
  ⟨-6423287/1000000000, 285280029/1000000000⟩
def contact3509 : RatBall := localContactBall tau3509 center3509
def work3509 : RoundedTauEval :=
  evalTau precision tau3509 contact3509 logTwoBall

theorem center_sq3509 : (center3509.re : ℝ)^2 +
    (center3509.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3509]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3509 : work3509.theta.ok = true ∧
    work3509.jac.invOK = true ∧ acceptsUnitSq work3509.out = true := by decide +kernel

def cell3509 : CellCertificate where
  tauBall := tau3509
  contactCenter := center3509
  contactBall := contact3509
  work := work3509
  center_sq := center_sq3509
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3509.1
  jac_ok := checks3509.2.1
  accepted := checks3509.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438


