-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0100
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0100
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:38:37.305162+00:00
-- url     : https://prove2.me/theorems/375cfe39-b37c-4eaa-bd3f-f27ea269b1a5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0100` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0100` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0100` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0100 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0100.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0100 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0100

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0800 : RatBall :=
  ⟨⟨-11/32, 17/160⟩, 3/320⟩
def center0800 : GaussianRat :=
  ⟨-57851871/250000000, 6570369/100000000⟩
def contact0800 : RatBall := localContactBall tau0800 center0800
def work0800 : RoundedTauEval :=
  evalTau precision tau0800 contact0800 logTwoBall

theorem center_sq0800 : (center0800.re : ℝ)^2 +
    (center0800.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0800]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0800 : work0800.theta.ok = true ∧
    work0800.jac.invOK = true ∧ acceptsUnitSq work0800.out = true := by decide +kernel

def cell0800 : CellCertificate where
  tauBall := tau0800
  contactCenter := center0800
  contactBall := contact0800
  work := work0800
  center_sq := center_sq0800
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0800.1
  jac_ok := checks0800.2.1
  accepted := checks0800.2.2

def tau0801 : RatBall :=
  ⟨⟨-53/160, 17/160⟩, 3/320⟩
def center0801 : GaussianRat :=
  ⟨-44722969/200000000, 66230667/1000000000⟩
def contact0801 : RatBall := localContactBall tau0801 center0801
def work0801 : RoundedTauEval :=
  evalTau precision tau0801 contact0801 logTwoBall

theorem center_sq0801 : (center0801.re : ℝ)^2 +
    (center0801.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0801]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0801 : work0801.theta.ok = true ∧
    work0801.jac.invOK = true ∧ acceptsUnitSq work0801.out = true := by decide +kernel

def cell0801 : CellCertificate where
  tauBall := tau0801
  contactCenter := center0801
  contactBall := contact0801
  work := work0801
  center_sq := center_sq0801
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0801.1
  jac_ok := checks0801.2.1
  accepted := checks0801.2.2

def tau0802 : RatBall :=
  ⟨⟨-11/32, 19/160⟩, 3/320⟩
def center0802 : GaussianRat :=
  ⟨-231972447/1000000000, 73469819/1000000000⟩
def contact0802 : RatBall := localContactBall tau0802 center0802
def work0802 : RoundedTauEval :=
  evalTau precision tau0802 contact0802 logTwoBall

theorem center_sq0802 : (center0802.re : ℝ)^2 +
    (center0802.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0802]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0802 : work0802.theta.ok = true ∧
    work0802.jac.invOK = true ∧ acceptsUnitSq work0802.out = true := by decide +kernel

def cell0802 : CellCertificate where
  tauBall := tau0802
  contactCenter := center0802
  contactBall := contact0802
  work := work0802
  center_sq := center_sq0802
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0802.1
  jac_ok := checks0802.2.1
  accepted := checks0802.2.2

def tau0803 : RatBall :=
  ⟨⟨-53/160, 19/160⟩, 3/320⟩
def center0803 : GaussianRat :=
  ⟨-56041997/250000000, 74061203/1000000000⟩
def contact0803 : RatBall := localContactBall tau0803 center0803
def work0803 : RoundedTauEval :=
  evalTau precision tau0803 contact0803 logTwoBall

theorem center_sq0803 : (center0803.re : ℝ)^2 +
    (center0803.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0803]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0803 : work0803.theta.ok = true ∧
    work0803.jac.invOK = true ∧ acceptsUnitSq work0803.out = true := by decide +kernel

def cell0803 : CellCertificate where
  tauBall := tau0803
  contactCenter := center0803
  contactBall := contact0803
  work := work0803
  center_sq := center_sq0803
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0803.1
  jac_ok := checks0803.2.1
  accepted := checks0803.2.2

def tau0804 : RatBall :=
  ⟨⟨-11/32, 21/160⟩, 3/320⟩
def center0804 : GaussianRat :=
  ⟨-232602861/1000000000, 81248009/1000000000⟩
def contact0804 : RatBall := localContactBall tau0804 center0804
def work0804 : RoundedTauEval :=
  evalTau precision tau0804 contact0804 logTwoBall

theorem center_sq0804 : (center0804.re : ℝ)^2 +
    (center0804.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0804]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0804 : work0804.theta.ok = true ∧
    work0804.jac.invOK = true ∧ acceptsUnitSq work0804.out = true := by decide +kernel

def cell0804 : CellCertificate where
  tauBall := tau0804
  contactCenter := center0804
  contactBall := contact0804
  work := work0804
  center_sq := center_sq0804
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0804.1
  jac_ok := checks0804.2.1
  accepted := checks0804.2.2

def tau0805 : RatBall :=
  ⟨⟨-53/160, 21/160⟩, 3/320⟩
def center0805 : GaussianRat :=
  ⟨-224785281/1000000000, 4095231/50000000⟩
def contact0805 : RatBall := localContactBall tau0805 center0805
def work0805 : RoundedTauEval :=
  evalTau precision tau0805 contact0805 logTwoBall

theorem center_sq0805 : (center0805.re : ℝ)^2 +
    (center0805.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0805]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0805 : work0805.theta.ok = true ∧
    work0805.jac.invOK = true ∧ acceptsUnitSq work0805.out = true := by decide +kernel

def cell0805 : CellCertificate where
  tauBall := tau0805
  contactCenter := center0805
  contactBall := contact0805
  work := work0805
  center_sq := center_sq0805
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0805.1
  jac_ok := checks0805.2.1
  accepted := checks0805.2.2

def tau0806 : RatBall :=
  ⟨⟨-11/32, 23/160⟩, 3/320⟩
def center0806 : GaussianRat :=
  ⟨-58324897/250000000, 11129939/125000000⟩
def contact0806 : RatBall := localContactBall tau0806 center0806
def work0806 : RoundedTauEval :=
  evalTau precision tau0806 contact0806 logTwoBall

theorem center_sq0806 : (center0806.re : ℝ)^2 +
    (center0806.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0806]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0806 : work0806.theta.ok = true ∧
    work0806.jac.invOK = true ∧ acceptsUnitSq work0806.out = true := by decide +kernel

def cell0806 : CellCertificate where
  tauBall := tau0806
  contactCenter := center0806
  contactBall := contact0806
  work := work0806
  center_sq := center_sq0806
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0806.1
  jac_ok := checks0806.2.1
  accepted := checks0806.2.2

def tau0807 : RatBall :=
  ⟨⟨-53/160, 23/160⟩, 3/320⟩
def center0807 : GaussianRat :=
  ⟨-225467593/1000000000, 89762261/1000000000⟩
def contact0807 : RatBall := localContactBall tau0807 center0807
def work0807 : RoundedTauEval :=
  evalTau precision tau0807 contact0807 logTwoBall

theorem center_sq0807 : (center0807.re : ℝ)^2 +
    (center0807.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0807]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0807 : work0807.theta.ok = true ∧
    work0807.jac.invOK = true ∧ acceptsUnitSq work0807.out = true := by decide +kernel

def cell0807 : CellCertificate where
  tauBall := tau0807
  contactCenter := center0807
  contactBall := contact0807
  work := work0807
  center_sq := center_sq0807
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0807.1
  jac_ok := checks0807.2.1
  accepted := checks0807.2.2

def cells : List CellCertificate := [cell0800, cell0801, cell0802, cell0803, cell0804, cell0805, cell0806, cell0807]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0100

end


