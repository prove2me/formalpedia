-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0063
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0063
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:03:34.835711+00:00
-- url     : https://prove2.me/theorems/882b0b82-26da-4c30-8edd-8c5caf07b5c8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0063` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0063` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0063` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0063 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0063.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0063 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0063

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0504 : RatBall :=
  ⟨⟨-59/160, -23/160⟩, 3/320⟩
def center0504 : GaussianRat :=
  ⟨-248760621/1000000000, -43775671/500000000⟩
def contact0504 : RatBall := localContactBall tau0504 center0504
def work0504 : RoundedTauEval :=
  evalTau precision tau0504 contact0504 logTwoBall

theorem center_sq0504 : (center0504.re : ℝ)^2 +
    (center0504.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0504]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0504 : work0504.theta.ok = true ∧
    work0504.jac.invOK = true ∧ acceptsUnitSq work0504.out = true := by decide +kernel

def cell0504 : CellCertificate where
  tauBall := tau0504
  contactCenter := center0504
  contactBall := contact0504
  work := work0504
  center_sq := center_sq0504
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0504.1
  jac_ok := checks0504.2.1
  accepted := checks0504.2.2

def tau0505 : RatBall :=
  ⟨⟨-57/160, -23/160⟩, 3/320⟩
def center0505 : GaussianRat :=
  ⟨-30133041/125000000, -17660441/200000000⟩
def contact0505 : RatBall := localContactBall tau0505 center0505
def work0505 : RoundedTauEval :=
  evalTau precision tau0505 contact0505 logTwoBall

theorem center_sq0505 : (center0505.re : ℝ)^2 +
    (center0505.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0505]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0505 : work0505.theta.ok = true ∧
    work0505.jac.invOK = true ∧ acceptsUnitSq work0505.out = true := by decide +kernel

def cell0505 : CellCertificate where
  tauBall := tau0505
  contactCenter := center0505
  contactBall := contact0505
  work := work0505
  center_sq := center_sq0505
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0505.1
  jac_ok := checks0505.2.1
  accepted := checks0505.2.2

def tau0506 : RatBall :=
  ⟨⟨-59/160, -21/160⟩, 3/320⟩
def center0506 : GaussianRat :=
  ⟨-124018963/500000000, -79895753/1000000000⟩
def contact0506 : RatBall := localContactBall tau0506 center0506
def work0506 : RoundedTauEval :=
  evalTau precision tau0506 contact0506 logTwoBall

theorem center_sq0506 : (center0506.re : ℝ)^2 +
    (center0506.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0506]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0506 : work0506.theta.ok = true ∧
    work0506.jac.invOK = true ∧ acceptsUnitSq work0506.out = true := by decide +kernel

def cell0506 : CellCertificate where
  tauBall := tau0506
  contactCenter := center0506
  contactBall := contact0506
  work := work0506
  center_sq := center_sq0506
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0506.1
  jac_ok := checks0506.2.1
  accepted := checks0506.2.2

def tau0507 : RatBall :=
  ⟨⟨-57/160, -21/160⟩, 3/320⟩
def center0507 : GaussianRat :=
  ⟨-120177071/500000000, -16115617/200000000⟩
def contact0507 : RatBall := localContactBall tau0507 center0507
def work0507 : RoundedTauEval :=
  evalTau precision tau0507 contact0507 logTwoBall

theorem center_sq0507 : (center0507.re : ℝ)^2 +
    (center0507.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0507]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0507 : work0507.theta.ok = true ∧
    work0507.jac.invOK = true ∧ acceptsUnitSq work0507.out = true := by decide +kernel

def cell0507 : CellCertificate where
  tauBall := tau0507
  contactCenter := center0507
  contactBall := contact0507
  work := work0507
  center_sq := center_sq0507
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0507.1
  jac_ok := checks0507.2.1
  accepted := checks0507.2.2

def tau0508 : RatBall :=
  ⟨⟨-61/160, -19/160⟩, 3/320⟩
def center0508 : GaussianRat :=
  ⟨-31873559/125000000, -7162653/100000000⟩
def contact0508 : RatBall := localContactBall tau0508 center0508
def work0508 : RoundedTauEval :=
  evalTau precision tau0508 contact0508 logTwoBall

theorem center_sq0508 : (center0508.re : ℝ)^2 +
    (center0508.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0508]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0508 : work0508.theta.ok = true ∧
    work0508.jac.invOK = true ∧ acceptsUnitSq work0508.out = true := by decide +kernel

def cell0508 : CellCertificate where
  tauBall := tau0508
  contactCenter := center0508
  contactBall := contact0508
  work := work0508
  center_sq := center_sq0508
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0508.1
  jac_ok := checks0508.2.1
  accepted := checks0508.2.2

def tau0509 : RatBall :=
  ⟨⟨-61/160, -17/160⟩, 3/320⟩
def center0509 : GaussianRat :=
  ⟨-254392641/1000000000, -20019/312500⟩
def contact0509 : RatBall := localContactBall tau0509 center0509
def work0509 : RoundedTauEval :=
  evalTau precision tau0509 contact0509 logTwoBall

theorem center_sq0509 : (center0509.re : ℝ)^2 +
    (center0509.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0509]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0509 : work0509.theta.ok = true ∧
    work0509.jac.invOK = true ∧ acceptsUnitSq work0509.out = true := by decide +kernel

def cell0509 : CellCertificate where
  tauBall := tau0509
  contactCenter := center0509
  contactBall := contact0509
  work := work0509
  center_sq := center_sq0509
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0509.1
  jac_ok := checks0509.2.1
  accepted := checks0509.2.2

def tau0510 : RatBall :=
  ⟨⟨-59/160, -19/160⟩, 3/320⟩
def center0510 : GaussianRat :=
  ⟨-247383851/1000000000, -72251673/1000000000⟩
def contact0510 : RatBall := localContactBall tau0510 center0510
def work0510 : RoundedTauEval :=
  evalTau precision tau0510 contact0510 logTwoBall

theorem center_sq0510 : (center0510.re : ℝ)^2 +
    (center0510.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0510]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0510 : work0510.theta.ok = true ∧
    work0510.jac.invOK = true ∧ acceptsUnitSq work0510.out = true := by decide +kernel

def cell0510 : CellCertificate where
  tauBall := tau0510
  contactCenter := center0510
  contactBall := contact0510
  work := work0510
  center_sq := center_sq0510
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0510.1
  jac_ok := checks0510.2.1
  accepted := checks0510.2.2

def tau0511 : RatBall :=
  ⟨⟨-57/160, -19/160⟩, 3/320⟩
def center0511 : GaussianRat :=
  ⟨-239711471/1000000000, -72866371/1000000000⟩
def contact0511 : RatBall := localContactBall tau0511 center0511
def work0511 : RoundedTauEval :=
  evalTau precision tau0511 contact0511 logTwoBall

theorem center_sq0511 : (center0511.re : ℝ)^2 +
    (center0511.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0511]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0511 : work0511.theta.ok = true ∧
    work0511.jac.invOK = true ∧ acceptsUnitSq work0511.out = true := by decide +kernel

def cell0511 : CellCertificate where
  tauBall := tau0511
  contactCenter := center0511
  contactBall := contact0511
  work := work0511
  center_sq := center_sq0511
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0511.1
  jac_ok := checks0511.2.1
  accepted := checks0511.2.2

def cells : List CellCertificate := [cell0504, cell0505, cell0506, cell0507, cell0508, cell0509, cell0510, cell0511]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0063

end


