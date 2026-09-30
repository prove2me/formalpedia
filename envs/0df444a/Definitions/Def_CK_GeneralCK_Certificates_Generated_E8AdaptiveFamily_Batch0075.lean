-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0075
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0075
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:07:46.072365+00:00
-- url     : https://prove2.me/theorems/9a438b26-711b-4611-ba63-218a1e41d471
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0075` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0075` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0075` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0075 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0075.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0075 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0075

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0600 : RatBall :=
  ⟨⟨9/160, -9/32⟩, 3/320⟩
def center0600 : GaussianRat :=
  ⟨21205027/500000000, -199811247/1000000000⟩
def contact0600 : RatBall := localContactBall tau0600 center0600
def work0600 : RoundedTauEval :=
  evalTau precision tau0600 contact0600 logTwoBall

theorem center_sq0600 : (center0600.re : ℝ)^2 +
    (center0600.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0600]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0600 : work0600.theta.ok = true ∧
    work0600.jac.invOK = true ∧ acceptsUnitSq work0600.out = true := by decide +kernel

def cell0600 : CellCertificate where
  tauBall := tau0600
  contactCenter := center0600
  contactBall := contact0600
  work := work0600
  center_sq := center_sq0600
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0600.1
  jac_ok := checks0600.2.1
  accepted := checks0600.2.2

def tau0601 : RatBall :=
  ⟨⟨11/160, -9/32⟩, 3/320⟩
def center0601 : GaussianRat :=
  ⟨25896777/500000000, -199440199/1000000000⟩
def contact0601 : RatBall := localContactBall tau0601 center0601
def work0601 : RoundedTauEval :=
  evalTau precision tau0601 contact0601 logTwoBall

theorem center_sq0601 : (center0601.re : ℝ)^2 +
    (center0601.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0601]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0601 : work0601.theta.ok = true ∧
    work0601.jac.invOK = true ∧ acceptsUnitSq work0601.out = true := by decide +kernel

def cell0601 : CellCertificate where
  tauBall := tau0601
  contactCenter := center0601
  contactBall := contact0601
  work := work0601
  center_sq := center_sq0601
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0601.1
  jac_ok := checks0601.2.1
  accepted := checks0601.2.2

def tau0602 : RatBall :=
  ⟨⟨13/160, -47/160⟩, 3/320⟩
def center0602 : GaussianRat :=
  ⟨61646237/1000000000, -5209469/25000000⟩
def contact0602 : RatBall := localContactBall tau0602 center0602
def work0602 : RoundedTauEval :=
  evalTau precision tau0602 contact0602 logTwoBall

theorem center_sq0602 : (center0602.re : ℝ)^2 +
    (center0602.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0602]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0602 : work0602.theta.ok = true ∧
    work0602.jac.invOK = true ∧ acceptsUnitSq work0602.out = true := by decide +kernel

def cell0602 : CellCertificate where
  tauBall := tau0602
  contactCenter := center0602
  contactBall := contact0602
  work := work0602
  center_sq := center_sq0602
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0602.1
  jac_ok := checks0602.2.1
  accepted := checks0602.2.2

def tau0603 : RatBall :=
  ⟨⟨3/32, -47/160⟩, 3/320⟩
def center0603 : GaussianRat :=
  ⟨71049459/1000000000, -207833009/1000000000⟩
def contact0603 : RatBall := localContactBall tau0603 center0603
def work0603 : RoundedTauEval :=
  evalTau precision tau0603 contact0603 logTwoBall

theorem center_sq0603 : (center0603.re : ℝ)^2 +
    (center0603.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0603]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0603 : work0603.theta.ok = true ∧
    work0603.jac.invOK = true ∧ acceptsUnitSq work0603.out = true := by decide +kernel

def cell0603 : CellCertificate where
  tauBall := tau0603
  contactCenter := center0603
  contactBall := contact0603
  work := work0603
  center_sq := center_sq0603
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0603.1
  jac_ok := checks0603.2.1
  accepted := checks0603.2.2

def tau0604 : RatBall :=
  ⟨⟨13/160, -9/32⟩, 3/320⟩
def center0604 : GaussianRat :=
  ⟨30576347/500000000, -99498463/500000000⟩
def contact0604 : RatBall := localContactBall tau0604 center0604
def work0604 : RoundedTauEval :=
  evalTau precision tau0604 contact0604 logTwoBall

theorem center_sq0604 : (center0604.re : ℝ)^2 +
    (center0604.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0604]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0604 : work0604.theta.ok = true ∧
    work0604.jac.invOK = true ∧ acceptsUnitSq work0604.out = true := by decide +kernel

def cell0604 : CellCertificate where
  tauBall := tau0604
  contactCenter := center0604
  contactBall := contact0604
  work := work0604
  center_sq := center_sq0604
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0604.1
  jac_ok := checks0604.2.1
  accepted := checks0604.2.2

def tau0605 : RatBall :=
  ⟨⟨3/32, -9/32⟩, 3/320⟩
def center0605 : GaussianRat :=
  ⟨17620809/250000000, -24810311/125000000⟩
def contact0605 : RatBall := localContactBall tau0605 center0605
def work0605 : RoundedTauEval :=
  evalTau precision tau0605 contact0605 logTwoBall

theorem center_sq0605 : (center0605.re : ℝ)^2 +
    (center0605.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0605]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0605 : work0605.theta.ok = true ∧
    work0605.jac.invOK = true ∧ acceptsUnitSq work0605.out = true := by decide +kernel

def cell0605 : CellCertificate where
  tauBall := tau0605
  contactCenter := center0605
  contactBall := contact0605
  work := work0605
  center_sq := center_sq0605
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0605.1
  jac_ok := checks0605.2.1
  accepted := checks0605.2.2

def tau0606 : RatBall :=
  ⟨⟨17/160, -47/160⟩, 3/320⟩
def center0606 : GaussianRat :=
  ⟨20104647/250000000, -10360657/50000000⟩
def contact0606 : RatBall := localContactBall tau0606 center0606
def work0606 : RoundedTauEval :=
  evalTau precision tau0606 contact0606 logTwoBall

theorem center_sq0606 : (center0606.re : ℝ)^2 +
    (center0606.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0606]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0606 : work0606.theta.ok = true ∧
    work0606.jac.invOK = true ∧ acceptsUnitSq work0606.out = true := by decide +kernel

def cell0606 : CellCertificate where
  tauBall := tau0606
  contactCenter := center0606
  contactBall := contact0606
  work := work0606
  center_sq := center_sq0606
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0606.1
  jac_ok := checks0606.2.1
  accepted := checks0606.2.2

def tau0607 : RatBall :=
  ⟨⟨19/160, -47/160⟩, 3/320⟩
def center0607 : GaussianRat :=
  ⟨89749431/1000000000, -206520639/1000000000⟩
def contact0607 : RatBall := localContactBall tau0607 center0607
def work0607 : RoundedTauEval :=
  evalTau precision tau0607 contact0607 logTwoBall

theorem center_sq0607 : (center0607.re : ℝ)^2 +
    (center0607.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0607]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0607 : work0607.theta.ok = true ∧
    work0607.jac.invOK = true ∧ acceptsUnitSq work0607.out = true := by decide +kernel

def cell0607 : CellCertificate where
  tauBall := tau0607
  contactCenter := center0607
  contactBall := contact0607
  work := work0607
  center_sq := center_sq0607
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0607.1
  jac_ok := checks0607.2.1
  accepted := checks0607.2.2

def cells : List CellCertificate := [cell0600, cell0601, cell0602, cell0603, cell0604, cell0605, cell0606, cell0607]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0075

end


