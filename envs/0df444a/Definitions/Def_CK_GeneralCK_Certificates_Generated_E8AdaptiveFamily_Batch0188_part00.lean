-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0188_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0188_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:24:08.510904+00:00
-- url     : https://prove2.me/theorems/80e85146-6957-42a5-a323-77de305af06d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0188 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1504 : RatBall :=
  ⟨⟨-11/320, -119/320⟩, 3/640⟩
def center1504 : GaussianRat :=
  ⟨-27795199/1000000000, -135428181/500000000⟩
def contact1504 : RatBall := localContactBall tau1504 center1504
def work1504 : RoundedTauEval :=
  evalTau precision tau1504 contact1504 logTwoBall

theorem center_sq1504 : (center1504.re : ℝ)^2 +
    (center1504.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1504]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1504 : work1504.theta.ok = true ∧
    work1504.jac.invOK = true ∧ acceptsUnitSq work1504.out = true := by decide +kernel

def cell1504 : CellCertificate where
  tauBall := tau1504
  contactCenter := center1504
  contactBall := contact1504
  work := work1504
  center_sq := center_sq1504
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1504.1
  jac_ok := checks1504.2.1
  accepted := checks1504.2.2

def tau1505 : RatBall :=
  ⟨⟨-9/320, -119/320⟩, 3/640⟩
def center1505 : GaussianRat :=
  ⟨-22747453/1000000000, -270997951/1000000000⟩
def contact1505 : RatBall := localContactBall tau1505 center1505
def work1505 : RoundedTauEval :=
  evalTau precision tau1505 contact1505 logTwoBall

theorem center_sq1505 : (center1505.re : ℝ)^2 +
    (center1505.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1505]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1505 : work1505.theta.ok = true ∧
    work1505.jac.invOK = true ∧ acceptsUnitSq work1505.out = true := by decide +kernel

def cell1505 : CellCertificate where
  tauBall := tau1505
  contactCenter := center1505
  contactBall := contact1505
  work := work1505
  center_sq := center_sq1505
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1505.1
  jac_ok := checks1505.2.1
  accepted := checks1505.2.2

def tau1506 : RatBall :=
  ⟨⟨-11/320, -117/320⟩, 3/640⟩
def center1506 : GaussianRat :=
  ⟨-863803/31250000, -33228071/125000000⟩
def contact1506 : RatBall := localContactBall tau1506 center1506
def work1506 : RoundedTauEval :=
  evalTau precision tau1506 contact1506 logTwoBall

theorem center_sq1506 : (center1506.re : ℝ)^2 +
    (center1506.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1506]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1506 : work1506.theta.ok = true ∧
    work1506.jac.invOK = true ∧ acceptsUnitSq work1506.out = true := by decide +kernel

def cell1506 : CellCertificate where
  tauBall := tau1506
  contactCenter := center1506
  contactBall := contact1506
  work := work1506
  center_sq := center_sq1506
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1506.1
  jac_ok := checks1506.2.1
  accepted := checks1506.2.2

def tau1507 : RatBall :=
  ⟨⟨-9/320, -117/320⟩, 3/640⟩
def center1507 : GaussianRat :=
  ⟨-4524341/200000000, -53192453/200000000⟩
def contact1507 : RatBall := localContactBall tau1507 center1507
def work1507 : RoundedTauEval :=
  evalTau precision tau1507 contact1507 logTwoBall

theorem center_sq1507 : (center1507.re : ℝ)^2 +
    (center1507.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1507]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1507 : work1507.theta.ok = true ∧
    work1507.jac.invOK = true ∧ acceptsUnitSq work1507.out = true := by decide +kernel

def cell1507 : CellCertificate where
  tauBall := tau1507
  contactCenter := center1507
  contactBall := contact1507
  work := work1507
  center_sq := center_sq1507
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1507.1
  jac_ok := checks1507.2.1
  accepted := checks1507.2.2

def tau1508 : RatBall :=
  ⟨⟨-3/64, -23/64⟩, 3/640⟩
def center1508 : GaussianRat :=
  ⟨-37465331/1000000000, -260472693/1000000000⟩
def contact1508 : RatBall := localContactBall tau1508 center1508
def work1508 : RoundedTauEval :=
  evalTau precision tau1508 contact1508 logTwoBall

theorem center_sq1508 : (center1508.re : ℝ)^2 +
    (center1508.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1508]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1508 : work1508.theta.ok = true ∧
    work1508.jac.invOK = true ∧ acceptsUnitSq work1508.out = true := by decide +kernel

def cell1508 : CellCertificate where
  tauBall := tau1508
  contactCenter := center1508
  contactBall := contact1508
  work := work1508
  center_sq := center_sq1508
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1508.1
  jac_ok := checks1508.2.1
  accepted := checks1508.2.2

def tau1509 : RatBall :=
  ⟨⟨-13/320, -23/64⟩, 3/640⟩
def center1509 : GaussianRat :=
  ⟨-32481297/1000000000, -260659621/1000000000⟩
def contact1509 : RatBall := localContactBall tau1509 center1509
def work1509 : RoundedTauEval :=
  evalTau precision tau1509 contact1509 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188


