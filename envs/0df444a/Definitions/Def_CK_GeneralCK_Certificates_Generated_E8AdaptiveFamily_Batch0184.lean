-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0184
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0184
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:02:08.404351+00:00
-- url     : https://prove2.me/theorems/de7977bb-ac2b-4fb6-bfc9-82f164540c4f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0184` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0184` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0184` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0184 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0184.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0184 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0184

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1472 : RatBall :=
  ⟨⟨-21/320, -119/320⟩, 3/640⟩
def center1472 : GaussianRat :=
  ⟨-26476749/500000000, -33716241/125000000⟩
def contact1472 : RatBall := localContactBall tau1472 center1472
def work1472 : RoundedTauEval :=
  evalTau precision tau1472 contact1472 logTwoBall

theorem center_sq1472 : (center1472.re : ℝ)^2 +
    (center1472.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1472]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1472 : work1472.theta.ok = true ∧
    work1472.jac.invOK = true ∧ acceptsUnitSq work1472.out = true := by decide +kernel

def cell1472 : CellCertificate where
  tauBall := tau1472
  contactCenter := center1472
  contactBall := contact1472
  work := work1472
  center_sq := center_sq1472
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1472.1
  jac_ok := checks1472.2.1
  accepted := checks1472.2.2

def tau1473 : RatBall :=
  ⟨⟨-23/320, -117/320⟩, 3/640⟩
def center1473 : GaussianRat :=
  ⟨-57646751/1000000000, -52885917/200000000⟩
def contact1473 : RatBall := localContactBall tau1473 center1473
def work1473 : RoundedTauEval :=
  evalTau precision tau1473 contact1473 logTwoBall

theorem center_sq1473 : (center1473.re : ℝ)^2 +
    (center1473.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1473]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1473 : work1473.theta.ok = true ∧
    work1473.jac.invOK = true ∧ acceptsUnitSq work1473.out = true := by decide +kernel

def cell1473 : CellCertificate where
  tauBall := tau1473
  contactCenter := center1473
  contactBall := contact1473
  work := work1473
  center_sq := center_sq1473
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1473.1
  jac_ok := checks1473.2.1
  accepted := checks1473.2.2

def tau1474 : RatBall :=
  ⟨⟨-21/320, -117/320⟩, 3/640⟩
def center1474 : GaussianRat :=
  ⟨-52663303/1000000000, -52945801/200000000⟩
def contact1474 : RatBall := localContactBall tau1474 center1474
def work1474 : RoundedTauEval :=
  evalTau precision tau1474 contact1474 logTwoBall

theorem center_sq1474 : (center1474.re : ℝ)^2 +
    (center1474.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1474]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1474 : work1474.theta.ok = true ∧
    work1474.jac.invOK = true ∧ acceptsUnitSq work1474.out = true := by decide +kernel

def cell1474 : CellCertificate where
  tauBall := tau1474
  contactCenter := center1474
  contactBall := contact1474
  work := work1474
  center_sq := center_sq1474
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1474.1
  jac_ok := checks1474.2.1
  accepted := checks1474.2.2

def tau1475 : RatBall :=
  ⟨⟨-19/320, -119/320⟩, 3/640⟩
def center1475 : GaussianRat :=
  ⟨-47935117/1000000000, -2109457/7812500⟩
def contact1475 : RatBall := localContactBall tau1475 center1475
def work1475 : RoundedTauEval :=
  evalTau precision tau1475 contact1475 logTwoBall

theorem center_sq1475 : (center1475.re : ℝ)^2 +
    (center1475.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1475]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1475 : work1475.theta.ok = true ∧
    work1475.jac.invOK = true ∧ acceptsUnitSq work1475.out = true := by decide +kernel

def cell1475 : CellCertificate where
  tauBall := tau1475
  contactCenter := center1475
  contactBall := contact1475
  work := work1475
  center_sq := center_sq1475
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1475.1
  jac_ok := checks1475.2.1
  accepted := checks1475.2.2

def tau1476 : RatBall :=
  ⟨⟨-17/320, -119/320⟩, 3/640⟩
def center1476 : GaussianRat :=
  ⟨-42909337/1000000000, -135131799/500000000⟩
def contact1476 : RatBall := localContactBall tau1476 center1476
def work1476 : RoundedTauEval :=
  evalTau precision tau1476 contact1476 logTwoBall

theorem center_sq1476 : (center1476.re : ℝ)^2 +
    (center1476.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1476]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1476 : work1476.theta.ok = true ∧
    work1476.jac.invOK = true ∧ acceptsUnitSq work1476.out = true := by decide +kernel

def cell1476 : CellCertificate where
  tauBall := tau1476
  contactCenter := center1476
  contactBall := contact1476
  work := work1476
  center_sq := center_sq1476
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1476.1
  jac_ok := checks1476.2.1
  accepted := checks1476.2.2

def tau1477 : RatBall :=
  ⟨⟨-19/320, -117/320⟩, 3/640⟩
def center1477 : GaussianRat :=
  ⟨-23835959/500000000, -265001899/1000000000⟩
def contact1477 : RatBall := localContactBall tau1477 center1477
def work1477 : RoundedTauEval :=
  evalTau precision tau1477 contact1477 logTwoBall

theorem center_sq1477 : (center1477.re : ℝ)^2 +
    (center1477.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1477]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1477 : work1477.theta.ok = true ∧
    work1477.jac.invOK = true ∧ acceptsUnitSq work1477.out = true := by decide +kernel

def cell1477 : CellCertificate where
  tauBall := tau1477
  contactCenter := center1477
  contactBall := contact1477
  work := work1477
  center_sq := center_sq1477
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1477.1
  jac_ok := checks1477.2.1
  accepted := checks1477.2.2

def tau1478 : RatBall :=
  ⟨⟨-17/320, -117/320⟩, 3/640⟩
def center1478 : GaussianRat :=
  ⟨-10668331/250000000, -265248069/1000000000⟩
def contact1478 : RatBall := localContactBall tau1478 center1478
def work1478 : RoundedTauEval :=
  evalTau precision tau1478 contact1478 logTwoBall

theorem center_sq1478 : (center1478.re : ℝ)^2 +
    (center1478.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1478]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1478 : work1478.theta.ok = true ∧
    work1478.jac.invOK = true ∧ acceptsUnitSq work1478.out = true := by decide +kernel

def cell1478 : CellCertificate where
  tauBall := tau1478
  contactCenter := center1478
  contactBall := contact1478
  work := work1478
  center_sq := center_sq1478
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1478.1
  jac_ok := checks1478.2.1
  accepted := checks1478.2.2

def tau1479 : RatBall :=
  ⟨⟨-23/320, -23/64⟩, 3/640⟩
def center1479 : GaussianRat :=
  ⟨-5733843/100000000, -129731693/500000000⟩
def contact1479 : RatBall := localContactBall tau1479 center1479
def work1479 : RoundedTauEval :=
  evalTau precision tau1479 contact1479 logTwoBall

theorem center_sq1479 : (center1479.re : ℝ)^2 +
    (center1479.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1479]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1479 : work1479.theta.ok = true ∧
    work1479.jac.invOK = true ∧ acceptsUnitSq work1479.out = true := by decide +kernel

def cell1479 : CellCertificate where
  tauBall := tau1479
  contactCenter := center1479
  contactBall := contact1479
  work := work1479
  center_sq := center_sq1479
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1479.1
  jac_ok := checks1479.2.1
  accepted := checks1479.2.2

def cells : List CellCertificate := [cell1472, cell1473, cell1474, cell1475, cell1476, cell1477, cell1478, cell1479]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0184

end


