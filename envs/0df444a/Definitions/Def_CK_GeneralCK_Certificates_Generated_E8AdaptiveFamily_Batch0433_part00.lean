-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0433_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0433_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:14:54.953438+00:00
-- url     : https://prove2.me/theorems/2bb8286a-3143-41b0-bc12-e36fde70539d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0433 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3464 : RatBall :=
  ⟨⟨-27/640, 249/640⟩, 3/1280⟩
def center3464 : GaussianRat :=
  ⟨-34643579/1000000000, 56921471/200000000⟩
def contact3464 : RatBall := localContactBall tau3464 center3464
def work3464 : RoundedTauEval :=
  evalTau precision tau3464 contact3464 logTwoBall

theorem center_sq3464 : (center3464.re : ℝ)^2 +
    (center3464.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3464]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3464 : work3464.theta.ok = true ∧
    work3464.jac.invOK = true ∧ acceptsUnitSq work3464.out = true := by decide +kernel

def cell3464 : CellCertificate where
  tauBall := tau3464
  contactCenter := center3464
  contactBall := contact3464
  work := work3464
  center_sq := center_sq3464
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3464.1
  jac_ok := checks3464.2.1
  accepted := checks3464.2.2

def tau3465 : RatBall :=
  ⟨⟨-5/128, 249/640⟩, 3/1280⟩
def center3465 : GaussianRat :=
  ⟨-32083143/1000000000, 142353243/500000000⟩
def contact3465 : RatBall := localContactBall tau3465 center3465
def work3465 : RoundedTauEval :=
  evalTau precision tau3465 contact3465 logTwoBall

theorem center_sq3465 : (center3465.re : ℝ)^2 +
    (center3465.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3465]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3465 : work3465.theta.ok = true ∧
    work3465.jac.invOK = true ∧ acceptsUnitSq work3465.out = true := by decide +kernel

def cell3465 : CellCertificate where
  tauBall := tau3465
  contactCenter := center3465
  contactBall := contact3465
  work := work3465
  center_sq := center_sq3465
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3465.1
  jac_ok := checks3465.2.1
  accepted := checks3465.2.2

def tau3466 : RatBall :=
  ⟨⟨-27/640, 251/640⟩, 3/1280⟩
def center3466 : GaussianRat :=
  ⟨-17373599/500000000, 287170877/1000000000⟩
def contact3466 : RatBall := localContactBall tau3466 center3466
def work3466 : RoundedTauEval :=
  evalTau precision tau3466 contact3466 logTwoBall

theorem center_sq3466 : (center3466.re : ℝ)^2 +
    (center3466.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3466]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3466 : work3466.theta.ok = true ∧
    work3466.jac.invOK = true ∧ acceptsUnitSq work3466.out = true := by decide +kernel

def cell3466 : CellCertificate where
  tauBall := tau3466
  contactCenter := center3466
  contactBall := contact3466
  work := work3466
  center_sq := center_sq3466
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3466.1
  jac_ok := checks3466.2.1
  accepted := checks3466.2.2

def tau3467 : RatBall :=
  ⟨⟨-5/128, 251/640⟩, 3/1280⟩
def center3467 : GaussianRat :=
  ⟨-32179167/1000000000, 57454279/200000000⟩
def contact3467 : RatBall := localContactBall tau3467 center3467
def work3467 : RoundedTauEval :=
  evalTau precision tau3467 contact3467 logTwoBall

theorem center_sq3467 : (center3467.re : ℝ)^2 +
    (center3467.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3467]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3467 : work3467.theta.ok = true ∧
    work3467.jac.invOK = true ∧ acceptsUnitSq work3467.out = true := by decide +kernel

def cell3467 : CellCertificate where
  tauBall := tau3467
  contactCenter := center3467
  contactBall := contact3467
  work := work3467
  center_sq := center_sq3467
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3467.1
  jac_ok := checks3467.2.1
  accepted := checks3467.2.2

def tau3468 : RatBall :=
  ⟨⟨-31/640, 253/640⟩, 3/1280⟩
def center3468 : GaussianRat :=
  ⟨-9999803/250000000, 36189373/125000000⟩
def contact3468 : RatBall := localContactBall tau3468 center3468
def work3468 : RoundedTauEval :=
  evalTau precision tau3468 contact3468 logTwoBall

theorem center_sq3468 : (center3468.re : ℝ)^2 +
    (center3468.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3468]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3468 : work3468.theta.ok = true ∧
    work3468.jac.invOK = true ∧ acceptsUnitSq work3468.out = true := by decide +kernel

def cell3468 : CellCertificate where
  tauBall := tau3468
  contactCenter := center3468
  contactBall := contact3468
  work := work3468
  center_sq := center_sq3468
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3468.1
  jac_ok := checks3468.2.1
  accepted := checks3468.2.2

def tau3469 : RatBall :=
  ⟨⟨-29/640, 253/640⟩, 3/1280⟩
def center3469 : GaussianRat :=
  ⟨-18713263/500000000, 289632371/1000000000⟩
def contact3469 : RatBall := localContactBall tau3469 center3469
def work3469 : RoundedTauEval :=
  evalTau precision tau3469 contact3469 logTwoBall

theorem center_sq3469 : (center3469.re : ℝ)^2 +
    (center3469.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3469]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3469 : work3469.theta.ok = true ∧
    work3469.jac.invOK = true ∧ acceptsUnitSq work3469.out = true := by decide +kernel

def cell3469 : CellCertificate where
  tauBall := tau3469
  contactCenter := center3469
  contactBall := contact3469
  work := work3469
  center_sq := center_sq3469
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3469.1
  jac_ok := checks3469.2.1
  accepted := checks3469.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433


