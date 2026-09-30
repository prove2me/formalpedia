-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0190
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0190
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:42:40.375638+00:00
-- url     : https://prove2.me/theorems/d6b73017-31ae-4c9d-93a8-328d443d8c05
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0190` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0190` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0190` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0190 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0190.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0190 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0190

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1520 : RatBall :=
  ⟨⟨-3/320, -119/320⟩, 3/640⟩
def center1520 : GaussianRat :=
  ⟨-3793023/500000000, -135626627/500000000⟩
def contact1520 : RatBall := localContactBall tau1520 center1520
def work1520 : RoundedTauEval :=
  evalTau precision tau1520 contact1520 logTwoBall

theorem center_sq1520 : (center1520.re : ℝ)^2 +
    (center1520.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1520]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1520 : work1520.theta.ok = true ∧
    work1520.jac.invOK = true ∧ acceptsUnitSq work1520.out = true := by decide +kernel

def cell1520 : CellCertificate where
  tauBall := tau1520
  contactCenter := center1520
  contactBall := contact1520
  work := work1520
  center_sq := center_sq1520
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1520.1
  jac_ok := checks1520.2.1
  accepted := checks1520.2.2

def tau1521 : RatBall :=
  ⟨⟨-1/320, -119/320⟩, 3/640⟩
def center1521 : GaussianRat :=
  ⟨-1264407/500000000, -33910207/125000000⟩
def contact1521 : RatBall := localContactBall tau1521 center1521
def work1521 : RoundedTauEval :=
  evalTau precision tau1521 contact1521 logTwoBall

theorem center_sq1521 : (center1521.re : ℝ)^2 +
    (center1521.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1521]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1521 : work1521.theta.ok = true ∧
    work1521.jac.invOK = true ∧ acceptsUnitSq work1521.out = true := by decide +kernel

def cell1521 : CellCertificate where
  tauBall := tau1521
  contactCenter := center1521
  contactBall := contact1521
  work := work1521
  center_sq := center_sq1521
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1521.1
  jac_ok := checks1521.2.1
  accepted := checks1521.2.2

def tau1522 : RatBall :=
  ⟨⟨-3/320, -117/320⟩, 3/640⟩
def center1522 : GaussianRat :=
  ⟨-7544037/1000000000, -16638159/62500000⟩
def contact1522 : RatBall := localContactBall tau1522 center1522
def work1522 : RoundedTauEval :=
  evalTau precision tau1522 contact1522 logTwoBall

theorem center_sq1522 : (center1522.re : ℝ)^2 +
    (center1522.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1522]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1522 : work1522.theta.ok = true ∧
    work1522.jac.invOK = true ∧ acceptsUnitSq work1522.out = true := by decide +kernel

def cell1522 : CellCertificate where
  tauBall := tau1522
  contactCenter := center1522
  contactBall := contact1522
  work := work1522
  center_sq := center_sq1522
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1522.1
  jac_ok := checks1522.2.1
  accepted := checks1522.2.2

def tau1523 : RatBall :=
  ⟨⟨-1/320, -117/320⟩, 3/640⟩
def center1523 : GaussianRat :=
  ⟨-314351/125000000, -66559541/250000000⟩
def contact1523 : RatBall := localContactBall tau1523 center1523
def work1523 : RoundedTauEval :=
  evalTau precision tau1523 contact1523 logTwoBall

theorem center_sq1523 : (center1523.re : ℝ)^2 +
    (center1523.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1523]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1523 : work1523.theta.ok = true ∧
    work1523.jac.invOK = true ∧ acceptsUnitSq work1523.out = true := by decide +kernel

def cell1523 : CellCertificate where
  tauBall := tau1523
  contactCenter := center1523
  contactBall := contact1523
  work := work1523
  center_sq := center_sq1523
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1523.1
  jac_ok := checks1523.2.1
  accepted := checks1523.2.2

def tau1524 : RatBall :=
  ⟨⟨-7/320, -23/64⟩, 3/640⟩
def center1524 : GaussianRat :=
  ⟨-350061/20000000, -130530621/500000000⟩
def contact1524 : RatBall := localContactBall tau1524 center1524
def work1524 : RoundedTauEval :=
  evalTau precision tau1524 contact1524 logTwoBall

theorem center_sq1524 : (center1524.re : ℝ)^2 +
    (center1524.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1524]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1524 : work1524.theta.ok = true ∧
    work1524.jac.invOK = true ∧ acceptsUnitSq work1524.out = true := by decide +kernel

def cell1524 : CellCertificate where
  tauBall := tau1524
  contactCenter := center1524
  contactBall := contact1524
  work := work1524
  center_sq := center_sq1524
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1524.1
  jac_ok := checks1524.2.1
  accepted := checks1524.2.2

def tau1525 : RatBall :=
  ⟨⟨-1/64, -23/64⟩, 3/640⟩
def center1525 : GaussianRat :=
  ⟨-1563007/125000000, -13057087/50000000⟩
def contact1525 : RatBall := localContactBall tau1525 center1525
def work1525 : RoundedTauEval :=
  evalTau precision tau1525 contact1525 logTwoBall

theorem center_sq1525 : (center1525.re : ℝ)^2 +
    (center1525.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1525]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1525 : work1525.theta.ok = true ∧
    work1525.jac.invOK = true ∧ acceptsUnitSq work1525.out = true := by decide +kernel

def cell1525 : CellCertificate where
  tauBall := tau1525
  contactCenter := center1525
  contactBall := contact1525
  work := work1525
  center_sq := center_sq1525
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1525.1
  jac_ok := checks1525.2.1
  accepted := checks1525.2.2

def tau1526 : RatBall :=
  ⟨⟨-7/320, -113/320⟩, 3/640⟩
def center1526 : GaussianRat :=
  ⟨-17410471/1000000000, -51215337/200000000⟩
def contact1526 : RatBall := localContactBall tau1526 center1526
def work1526 : RoundedTauEval :=
  evalTau precision tau1526 contact1526 logTwoBall

theorem center_sq1526 : (center1526.re : ℝ)^2 +
    (center1526.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1526]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1526 : work1526.theta.ok = true ∧
    work1526.jac.invOK = true ∧ acceptsUnitSq work1526.out = true := by decide +kernel

def cell1526 : CellCertificate where
  tauBall := tau1526
  contactCenter := center1526
  contactBall := contact1526
  work := work1526
  center_sq := center_sq1526
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1526.1
  jac_ok := checks1526.2.1
  accepted := checks1526.2.2

def tau1527 : RatBall :=
  ⟨⟨-1/64, -113/320⟩, 3/640⟩
def center1527 : GaussianRat :=
  ⟨-12437881/1000000000, -3201937/12500000⟩
def contact1527 : RatBall := localContactBall tau1527 center1527
def work1527 : RoundedTauEval :=
  evalTau precision tau1527 contact1527 logTwoBall

theorem center_sq1527 : (center1527.re : ℝ)^2 +
    (center1527.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1527]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1527 : work1527.theta.ok = true ∧
    work1527.jac.invOK = true ∧ acceptsUnitSq work1527.out = true := by decide +kernel

def cell1527 : CellCertificate where
  tauBall := tau1527
  contactCenter := center1527
  contactBall := contact1527
  work := work1527
  center_sq := center_sq1527
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1527.1
  jac_ok := checks1527.2.1
  accepted := checks1527.2.2

def cells : List CellCertificate := [cell1520, cell1521, cell1522, cell1523, cell1524, cell1525, cell1526, cell1527]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0190

end


