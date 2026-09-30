-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0325
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0325
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:03:32.014029+00:00
-- url     : https://prove2.me/theorems/61cfa620-0c67-4d9b-9930-b9a476a0065b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0325` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0325` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0325` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0325 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0325.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0325 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0325

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2600 : RatBall :=
  ⟨⟨-101/640, -47/128⟩, 3/1280⟩
def center2600 : GaussianRat :=
  ⟨-25032271/200000000, -809263/3125000⟩
def contact2600 : RatBall := localContactBall tau2600 center2600
def work2600 : RoundedTauEval :=
  evalTau precision tau2600 contact2600 logTwoBall

theorem center_sq2600 : (center2600.re : ℝ)^2 +
    (center2600.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2600]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2600 : work2600.theta.ok = true ∧
    work2600.jac.invOK = true ∧ acceptsUnitSq work2600.out = true := by decide +kernel

def cell2600 : CellCertificate where
  tauBall := tau2600
  contactCenter := center2600
  contactBall := contact2600
  work := work2600
  center_sq := center_sq2600
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2600.1
  jac_ok := checks2600.2.1
  accepted := checks2600.2.2

def tau2601 : RatBall :=
  ⟨⟨-103/640, -233/640⟩, 3/1280⟩
def center2601 : GaussianRat :=
  ⟨-1987999/15625000, -12812079/50000000⟩
def contact2601 : RatBall := localContactBall tau2601 center2601
def work2601 : RoundedTauEval :=
  evalTau precision tau2601 contact2601 logTwoBall

theorem center_sq2601 : (center2601.re : ℝ)^2 +
    (center2601.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2601]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2601 : work2601.theta.ok = true ∧
    work2601.jac.invOK = true ∧ acceptsUnitSq work2601.out = true := by decide +kernel

def cell2601 : CellCertificate where
  tauBall := tau2601
  contactCenter := center2601
  contactBall := contact2601
  work := work2601
  center_sq := center_sq2601
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2601.1
  jac_ok := checks2601.2.1
  accepted := checks2601.2.2

def tau2602 : RatBall :=
  ⟨⟨-101/640, -233/640⟩, 3/1280⟩
def center2602 : GaussianRat :=
  ⟨-124838069/1000000000, -64141351/250000000⟩
def contact2602 : RatBall := localContactBall tau2602 center2602
def work2602 : RoundedTauEval :=
  evalTau precision tau2602 contact2602 logTwoBall

theorem center_sq2602 : (center2602.re : ℝ)^2 +
    (center2602.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2602]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2602 : work2602.theta.ok = true ∧
    work2602.jac.invOK = true ∧ acceptsUnitSq work2602.out = true := by decide +kernel

def cell2602 : CellCertificate where
  tauBall := tau2602
  contactCenter := center2602
  contactBall := contact2602
  work := work2602
  center_sq := center_sq2602
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2602.1
  jac_ok := checks2602.2.1
  accepted := checks2602.2.2

def tau2603 : RatBall :=
  ⟨⟨-99/640, -47/128⟩, 3/1280⟩
def center2603 : GaussianRat :=
  ⟨-61378847/500000000, -129643433/500000000⟩
def contact2603 : RatBall := localContactBall tau2603 center2603
def work2603 : RoundedTauEval :=
  evalTau precision tau2603 contact2603 logTwoBall

theorem center_sq2603 : (center2603.re : ℝ)^2 +
    (center2603.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2603]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2603 : work2603.theta.ok = true ∧
    work2603.jac.invOK = true ∧ acceptsUnitSq work2603.out = true := by decide +kernel

def cell2603 : CellCertificate where
  tauBall := tau2603
  contactCenter := center2603
  contactBall := contact2603
  work := work2603
  center_sq := center_sq2603
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2603.1
  jac_ok := checks2603.2.1
  accepted := checks2603.2.2

def tau2604 : RatBall :=
  ⟨⟨-97/640, -47/128⟩, 3/1280⟩
def center2604 : GaussianRat :=
  ⟨-15043717/125000000, -259604029/1000000000⟩
def contact2604 : RatBall := localContactBall tau2604 center2604
def work2604 : RoundedTauEval :=
  evalTau precision tau2604 contact2604 logTwoBall

theorem center_sq2604 : (center2604.re : ℝ)^2 +
    (center2604.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2604]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2604 : work2604.theta.ok = true ∧
    work2604.jac.invOK = true ∧ acceptsUnitSq work2604.out = true := by decide +kernel

def cell2604 : CellCertificate where
  tauBall := tau2604
  contactCenter := center2604
  contactBall := contact2604
  work := work2604
  center_sq := center_sq2604
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2604.1
  jac_ok := checks2604.2.1
  accepted := checks2604.2.2

def tau2605 : RatBall :=
  ⟨⟨-99/640, -233/640⟩, 3/1280⟩
def center2605 : GaussianRat :=
  ⟨-122439891/1000000000, -51376761/200000000⟩
def contact2605 : RatBall := localContactBall tau2605 center2605
def work2605 : RoundedTauEval :=
  evalTau precision tau2605 contact2605 logTwoBall

theorem center_sq2605 : (center2605.re : ℝ)^2 +
    (center2605.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2605]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2605 : work2605.theta.ok = true ∧
    work2605.jac.invOK = true ∧ acceptsUnitSq work2605.out = true := by decide +kernel

def cell2605 : CellCertificate where
  tauBall := tau2605
  contactCenter := center2605
  contactBall := contact2605
  work := work2605
  center_sq := center_sq2605
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2605.1
  jac_ok := checks2605.2.1
  accepted := checks2605.2.2

def tau2606 : RatBall :=
  ⟨⟨-97/640, -233/640⟩, 3/1280⟩
def center2606 : GaussianRat :=
  ⟨-60018733/500000000, -257196731/1000000000⟩
def contact2606 : RatBall := localContactBall tau2606 center2606
def work2606 : RoundedTauEval :=
  evalTau precision tau2606 contact2606 logTwoBall

theorem center_sq2606 : (center2606.re : ℝ)^2 +
    (center2606.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2606]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2606 : work2606.theta.ok = true ∧
    work2606.jac.invOK = true ∧ acceptsUnitSq work2606.out = true := by decide +kernel

def cell2606 : CellCertificate where
  tauBall := tau2606
  contactCenter := center2606
  contactBall := contact2606
  work := work2606
  center_sq := center_sq2606
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2606.1
  jac_ok := checks2606.2.1
  accepted := checks2606.2.2

def tau2607 : RatBall :=
  ⟨⟨-111/640, -231/640⟩, 3/1280⟩
def center2607 : GaussianRat :=
  ⟨-34104423/250000000, -25252199/100000000⟩
def contact2607 : RatBall := localContactBall tau2607 center2607
def work2607 : RoundedTauEval :=
  evalTau precision tau2607 contact2607 logTwoBall

theorem center_sq2607 : (center2607.re : ℝ)^2 +
    (center2607.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2607]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2607 : work2607.theta.ok = true ∧
    work2607.jac.invOK = true ∧ acceptsUnitSq work2607.out = true := by decide +kernel

def cell2607 : CellCertificate where
  tauBall := tau2607
  contactCenter := center2607
  contactBall := contact2607
  work := work2607
  center_sq := center_sq2607
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2607.1
  jac_ok := checks2607.2.1
  accepted := checks2607.2.2

def cells : List CellCertificate := [cell2600, cell2601, cell2602, cell2603, cell2604, cell2605, cell2606, cell2607]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0325

end


