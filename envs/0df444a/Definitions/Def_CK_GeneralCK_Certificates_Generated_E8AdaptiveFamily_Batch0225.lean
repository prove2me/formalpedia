-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0225
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0225
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:01:56.670727+00:00
-- url     : https://prove2.me/theorems/4b157e91-c4b3-4705-815e-e74764081cd7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0225` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0225` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0225` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0225 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0225.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0225 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0225

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1800 : RatBall :=
  ⟨⟨15/64, -89/320⟩, 3/640⟩
def center1800 : GaussianRat :=
  ⟨21501427/125000000, -186088727/1000000000⟩
def contact1800 : RatBall := localContactBall tau1800 center1800
def work1800 : RoundedTauEval :=
  evalTau precision tau1800 contact1800 logTwoBall

theorem center_sq1800 : (center1800.re : ℝ)^2 +
    (center1800.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1800]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1800 : work1800.theta.ok = true ∧
    work1800.jac.invOK = true ∧ acceptsUnitSq work1800.out = true := by decide +kernel

def cell1800 : CellCertificate where
  tauBall := tau1800
  contactCenter := center1800
  contactBall := contact1800
  work := work1800
  center_sq := center_sq1800
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1800.1
  jac_ok := checks1800.2.1
  accepted := checks1800.2.2

def tau1801 : RatBall :=
  ⟨⟨77/320, -91/320⟩, 3/640⟩
def center1801 : GaussianRat :=
  ⟨17698031/100000000, -94910271/500000000⟩
def contact1801 : RatBall := localContactBall tau1801 center1801
def work1801 : RoundedTauEval :=
  evalTau precision tau1801 contact1801 logTwoBall

theorem center_sq1801 : (center1801.re : ℝ)^2 +
    (center1801.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1801]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1801 : work1801.theta.ok = true ∧
    work1801.jac.invOK = true ∧ acceptsUnitSq work1801.out = true := by decide +kernel

def cell1801 : CellCertificate where
  tauBall := tau1801
  contactCenter := center1801
  contactBall := contact1801
  work := work1801
  center_sq := center_sq1801
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1801.1
  jac_ok := checks1801.2.1
  accepted := checks1801.2.2

def tau1802 : RatBall :=
  ⟨⟨79/320, -91/320⟩, 3/640⟩
def center1802 : GaussianRat :=
  ⟨181318681/1000000000, -189181283/1000000000⟩
def contact1802 : RatBall := localContactBall tau1802 center1802
def work1802 : RoundedTauEval :=
  evalTau precision tau1802 contact1802 logTwoBall

theorem center_sq1802 : (center1802.re : ℝ)^2 +
    (center1802.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1802]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1802 : work1802.theta.ok = true ∧
    work1802.jac.invOK = true ∧ acceptsUnitSq work1802.out = true := by decide +kernel

def cell1802 : CellCertificate where
  tauBall := tau1802
  contactCenter := center1802
  contactBall := contact1802
  work := work1802
  center_sq := center_sq1802
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1802.1
  jac_ok := checks1802.2.1
  accepted := checks1802.2.2

def tau1803 : RatBall :=
  ⟨⟨77/320, -89/320⟩, 3/640⟩
def center1803 : GaussianRat :=
  ⟨88177939/500000000, -185479027/1000000000⟩
def contact1803 : RatBall := localContactBall tau1803 center1803
def work1803 : RoundedTauEval :=
  evalTau precision tau1803 contact1803 logTwoBall

theorem center_sq1803 : (center1803.re : ℝ)^2 +
    (center1803.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1803]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1803 : work1803.theta.ok = true ∧
    work1803.jac.invOK = true ∧ acceptsUnitSq work1803.out = true := by decide +kernel

def cell1803 : CellCertificate where
  tauBall := tau1803
  contactCenter := center1803
  contactBall := contact1803
  work := work1803
  center_sq := center_sq1803
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1803.1
  jac_ok := checks1803.2.1
  accepted := checks1803.2.2

def tau1804 : RatBall :=
  ⟨⟨79/320, -89/320⟩, 3/640⟩
def center1804 : GaussianRat :=
  ⟨22585333/125000000, -184857737/1000000000⟩
def contact1804 : RatBall := localContactBall tau1804 center1804
def work1804 : RoundedTauEval :=
  evalTau precision tau1804 contact1804 logTwoBall

theorem center_sq1804 : (center1804.re : ℝ)^2 +
    (center1804.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1804]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1804 : work1804.theta.ok = true ∧
    work1804.jac.invOK = true ∧ acceptsUnitSq work1804.out = true := by decide +kernel

def cell1804 : CellCertificate where
  tauBall := tau1804
  contactCenter := center1804
  contactBall := contact1804
  work := work1804
  center_sq := center_sq1804
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1804.1
  jac_ok := checks1804.2.1
  accepted := checks1804.2.2

def tau1805 : RatBall :=
  ⟨⟨81/320, -19/64⟩, 3/640⟩
def center1805 : GaussianRat :=
  ⟨186989333/1000000000, -49293783/250000000⟩
def contact1805 : RatBall := localContactBall tau1805 center1805
def work1805 : RoundedTauEval :=
  evalTau precision tau1805 contact1805 logTwoBall

theorem center_sq1805 : (center1805.re : ℝ)^2 +
    (center1805.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1805]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1805 : work1805.theta.ok = true ∧
    work1805.jac.invOK = true ∧ acceptsUnitSq work1805.out = true := by decide +kernel

def cell1805 : CellCertificate where
  tauBall := tau1805
  contactCenter := center1805
  contactBall := contact1805
  work := work1805
  center_sq := center_sq1805
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1805.1
  jac_ok := checks1805.2.1
  accepted := checks1805.2.2

def tau1806 : RatBall :=
  ⟨⟨83/320, -19/64⟩, 3/640⟩
def center1806 : GaussianRat :=
  ⟨191313683/1000000000, -3929501/20000000⟩
def contact1806 : RatBall := localContactBall tau1806 center1806
def work1806 : RoundedTauEval :=
  evalTau precision tau1806 contact1806 logTwoBall

theorem center_sq1806 : (center1806.re : ℝ)^2 +
    (center1806.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1806]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1806 : work1806.theta.ok = true ∧
    work1806.jac.invOK = true ∧ acceptsUnitSq work1806.out = true := by decide +kernel

def cell1806 : CellCertificate where
  tauBall := tau1806
  contactCenter := center1806
  contactBall := contact1806
  work := work1806
  center_sq := center_sq1806
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1806.1
  jac_ok := checks1806.2.1
  accepted := checks1806.2.2

def tau1807 : RatBall :=
  ⟨⟨81/320, -93/320⟩, 3/640⟩
def center1807 : GaussianRat :=
  ⟨93152319/500000000, -24105877/125000000⟩
def contact1807 : RatBall := localContactBall tau1807 center1807
def work1807 : RoundedTauEval :=
  evalTau precision tau1807 contact1807 logTwoBall

theorem center_sq1807 : (center1807.re : ℝ)^2 +
    (center1807.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1807]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1807 : work1807.theta.ok = true ∧
    work1807.jac.invOK = true ∧ acceptsUnitSq work1807.out = true := by decide +kernel

def cell1807 : CellCertificate where
  tauBall := tau1807
  contactCenter := center1807
  contactBall := contact1807
  work := work1807
  center_sq := center_sq1807
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1807.1
  jac_ok := checks1807.2.1
  accepted := checks1807.2.2

def cells : List CellCertificate := [cell1800, cell1801, cell1802, cell1803, cell1804, cell1805, cell1806, cell1807]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0225

end


