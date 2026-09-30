-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0200
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0200
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:23:40.322949+00:00
-- url     : https://prove2.me/theorems/25718a7c-e7c1-4e7c-9c43-a261c7fc470a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0200` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0200` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0200` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0200 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0200.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0200 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0200

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1600 : RatBall :=
  ⟨⟨23/320, -113/320⟩, 3/640⟩
def center1600 : GaussianRat :=
  ⟨57038551/1000000000, -63630699/250000000⟩
def contact1600 : RatBall := localContactBall tau1600 center1600
def work1600 : RoundedTauEval :=
  evalTau precision tau1600 contact1600 logTwoBall

theorem center_sq1600 : (center1600.re : ℝ)^2 +
    (center1600.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1600]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1600 : work1600.theta.ok = true ∧
    work1600.jac.invOK = true ∧ acceptsUnitSq work1600.out = true := by decide +kernel

def cell1600 : CellCertificate where
  tauBall := tau1600
  contactCenter := center1600
  contactBall := contact1600
  work := work1600
  center_sq := center_sq1600
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1600.1
  jac_ok := checks1600.2.1
  accepted := checks1600.2.2

def tau1601 : RatBall :=
  ⟨⟨5/64, -119/320⟩, 3/640⟩
def center1601 : GaussianRat :=
  ⟨1574127/25000000, -53817447/200000000⟩
def contact1601 : RatBall := localContactBall tau1601 center1601
def work1601 : RoundedTauEval :=
  evalTau precision tau1601 contact1601 logTwoBall

theorem center_sq1601 : (center1601.re : ℝ)^2 +
    (center1601.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1601]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1601 : work1601.theta.ok = true ∧
    work1601.jac.invOK = true ∧ acceptsUnitSq work1601.out = true := by decide +kernel

def cell1601 : CellCertificate where
  tauBall := tau1601
  contactCenter := center1601
  contactBall := contact1601
  work := work1601
  center_sq := center_sq1601
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1601.1
  jac_ok := checks1601.2.1
  accepted := checks1601.2.2

def tau1602 : RatBall :=
  ⟨⟨27/320, -119/320⟩, 3/640⟩
def center1602 : GaussianRat :=
  ⟨33978407/500000000, -67181393/250000000⟩
def contact1602 : RatBall := localContactBall tau1602 center1602
def work1602 : RoundedTauEval :=
  evalTau precision tau1602 contact1602 logTwoBall

theorem center_sq1602 : (center1602.re : ℝ)^2 +
    (center1602.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1602]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1602 : work1602.theta.ok = true ∧
    work1602.jac.invOK = true ∧ acceptsUnitSq work1602.out = true := by decide +kernel

def cell1602 : CellCertificate where
  tauBall := tau1602
  contactCenter := center1602
  contactBall := contact1602
  work := work1602
  center_sq := center_sq1602
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1602.1
  jac_ok := checks1602.2.1
  accepted := checks1602.2.2

def tau1603 : RatBall :=
  ⟨⟨5/64, -117/320⟩, 3/640⟩
def center1603 : GaussianRat :=
  ⟨3131077/50000000, -66025963/250000000⟩
def contact1603 : RatBall := localContactBall tau1603 center1603
def work1603 : RoundedTauEval :=
  evalTau precision tau1603 contact1603 logTwoBall

theorem center_sq1603 : (center1603.re : ℝ)^2 +
    (center1603.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1603]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1603 : work1603.theta.ok = true ∧
    work1603.jac.invOK = true ∧ acceptsUnitSq work1603.out = true := by decide +kernel

def cell1603 : CellCertificate where
  tauBall := tau1603
  contactCenter := center1603
  contactBall := contact1603
  work := work1603
  center_sq := center_sq1603
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1603.1
  jac_ok := checks1603.2.1
  accepted := checks1603.2.2

def tau1604 : RatBall :=
  ⟨⟨27/320, -117/320⟩, 3/640⟩
def center1604 : GaussianRat :=
  ⟨844837/12500000, -131876019/500000000⟩
def contact1604 : RatBall := localContactBall tau1604 center1604
def work1604 : RoundedTauEval :=
  evalTau precision tau1604 contact1604 logTwoBall

theorem center_sq1604 : (center1604.re : ℝ)^2 +
    (center1604.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1604]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1604 : work1604.theta.ok = true ∧
    work1604.jac.invOK = true ∧ acceptsUnitSq work1604.out = true := by decide +kernel

def cell1604 : CellCertificate where
  tauBall := tau1604
  contactCenter := center1604
  contactBall := contact1604
  work := work1604
  center_sq := center_sq1604
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1604.1
  jac_ok := checks1604.2.1
  accepted := checks1604.2.2

def tau1605 : RatBall :=
  ⟨⟨29/320, -119/320⟩, 3/640⟩
def center1605 : GaussianRat :=
  ⟨14587643/200000000, -268337373/1000000000⟩
def contact1605 : RatBall := localContactBall tau1605 center1605
def work1605 : RoundedTauEval :=
  evalTau precision tau1605 contact1605 logTwoBall

theorem center_sq1605 : (center1605.re : ℝ)^2 +
    (center1605.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1605]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1605 : work1605.theta.ok = true ∧
    work1605.jac.invOK = true ∧ acceptsUnitSq work1605.out = true := by decide +kernel

def cell1605 : CellCertificate where
  tauBall := tau1605
  contactCenter := center1605
  contactBall := contact1605
  work := work1605
  center_sq := center_sq1605
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1605.1
  jac_ok := checks1605.2.1
  accepted := checks1605.2.2

def tau1606 : RatBall :=
  ⟨⟨31/320, -119/320⟩, 3/640⟩
def center1606 : GaussianRat :=
  ⟨77908577/1000000000, -267922911/1000000000⟩
def contact1606 : RatBall := localContactBall tau1606 center1606
def work1606 : RoundedTauEval :=
  evalTau precision tau1606 contact1606 logTwoBall

theorem center_sq1606 : (center1606.re : ℝ)^2 +
    (center1606.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1606]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1606 : work1606.theta.ok = true ∧
    work1606.jac.invOK = true ∧ acceptsUnitSq work1606.out = true := by decide +kernel

def cell1606 : CellCertificate where
  tauBall := tau1606
  contactCenter := center1606
  contactBall := contact1606
  work := work1606
  center_sq := center_sq1606
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1606.1
  jac_ok := checks1606.2.1
  accepted := checks1606.2.2

def tau1607 : RatBall :=
  ⟨⟨29/320, -117/320⟩, 3/640⟩
def center1607 : GaussianRat :=
  ⟨7254231/100000000, -263374389/1000000000⟩
def contact1607 : RatBall := localContactBall tau1607 center1607
def work1607 : RoundedTauEval :=
  evalTau precision tau1607 contact1607 logTwoBall

theorem center_sq1607 : (center1607.re : ℝ)^2 +
    (center1607.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1607]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1607 : work1607.theta.ok = true ∧
    work1607.jac.invOK = true ∧ acceptsUnitSq work1607.out = true := by decide +kernel

def cell1607 : CellCertificate where
  tauBall := tau1607
  contactCenter := center1607
  contactBall := contact1607
  work := work1607
  center_sq := center_sq1607
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1607.1
  jac_ok := checks1607.2.1
  accepted := checks1607.2.2

def cells : List CellCertificate := [cell1600, cell1601, cell1602, cell1603, cell1604, cell1605, cell1606, cell1607]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0200

end


