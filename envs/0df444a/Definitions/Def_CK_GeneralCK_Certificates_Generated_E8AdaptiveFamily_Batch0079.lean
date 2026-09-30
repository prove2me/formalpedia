-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0079
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0079
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:07:01.298165+00:00
-- url     : https://prove2.me/theorems/7f74582d-9c0d-475f-9320-5078e1cb9b53
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0079` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0079` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0079` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0079 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0079.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0079 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0079

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0632 : RatBall :=
  ⟨⟨5/32, -41/160⟩, 3/320⟩
def center0632 : GaussianRat :=
  ⟨114906151/1000000000, -176804909/1000000000⟩
def contact0632 : RatBall := localContactBall tau0632 center0632
def work0632 : RoundedTauEval :=
  evalTau precision tau0632 contact0632 logTwoBall

theorem center_sq0632 : (center0632.re : ℝ)^2 +
    (center0632.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0632]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0632 : work0632.theta.ok = true ∧
    work0632.jac.invOK = true ∧ acceptsUnitSq work0632.out = true := by decide +kernel

def cell0632 : CellCertificate where
  tauBall := tau0632
  contactCenter := center0632
  contactBall := contact0632
  work := work0632
  center_sq := center_sq0632
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0632.1
  jac_ok := checks0632.2.1
  accepted := checks0632.2.2

def tau0633 : RatBall :=
  ⟨⟨27/160, -41/160⟩, 3/320⟩
def center0633 : GaussianRat :=
  ⟨123867137/1000000000, -21999637/125000000⟩
def contact0633 : RatBall := localContactBall tau0633 center0633
def work0633 : RoundedTauEval :=
  evalTau precision tau0633 contact0633 logTwoBall

theorem center_sq0633 : (center0633.re : ℝ)^2 +
    (center0633.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0633]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0633 : work0633.theta.ok = true ∧
    work0633.jac.invOK = true ∧ acceptsUnitSq work0633.out = true := by decide +kernel

def cell0633 : CellCertificate where
  tauBall := tau0633
  contactCenter := center0633
  contactBall := contact0633
  work := work0633
  center_sq := center_sq0633
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0633.1
  jac_ok := checks0633.2.1
  accepted := checks0633.2.2

def tau0634 : RatBall :=
  ⟨⟨29/160, -43/160⟩, 3/320⟩
def center0634 : GaussianRat :=
  ⟨66845797/500000000, -18404523/100000000⟩
def contact0634 : RatBall := localContactBall tau0634 center0634
def work0634 : RoundedTauEval :=
  evalTau precision tau0634 contact0634 logTwoBall

theorem center_sq0634 : (center0634.re : ℝ)^2 +
    (center0634.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0634]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0634 : work0634.theta.ok = true ∧
    work0634.jac.invOK = true ∧ acceptsUnitSq work0634.out = true := by decide +kernel

def cell0634 : CellCertificate where
  tauBall := tau0634
  contactCenter := center0634
  contactBall := contact0634
  work := work0634
  center_sq := center_sq0634
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0634.1
  jac_ok := checks0634.2.1
  accepted := checks0634.2.2

def tau0635 : RatBall :=
  ⟨⟨31/160, -43/160⟩, 3/320⟩
def center0635 : GaussianRat :=
  ⟨71299541/500000000, -91537843/500000000⟩
def contact0635 : RatBall := localContactBall tau0635 center0635
def work0635 : RoundedTauEval :=
  evalTau precision tau0635 contact0635 logTwoBall

theorem center_sq0635 : (center0635.re : ℝ)^2 +
    (center0635.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0635]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0635 : work0635.theta.ok = true ∧
    work0635.jac.invOK = true ∧ acceptsUnitSq work0635.out = true := by decide +kernel

def cell0635 : CellCertificate where
  tauBall := tau0635
  contactCenter := center0635
  contactBall := contact0635
  work := work0635
  center_sq := center_sq0635
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0635.1
  jac_ok := checks0635.2.1
  accepted := checks0635.2.2

def tau0636 : RatBall :=
  ⟨⟨29/160, -41/160⟩, 3/320⟩
def center0636 : GaussianRat :=
  ⟨132776829/1000000000, -35027183/200000000⟩
def contact0636 : RatBall := localContactBall tau0636 center0636
def work0636 : RoundedTauEval :=
  evalTau precision tau0636 contact0636 logTwoBall

theorem center_sq0636 : (center0636.re : ℝ)^2 +
    (center0636.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0636]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0636 : work0636.theta.ok = true ∧
    work0636.jac.invOK = true ∧ acceptsUnitSq work0636.out = true := by decide +kernel

def cell0636 : CellCertificate where
  tauBall := tau0636
  contactCenter := center0636
  contactBall := contact0636
  work := work0636
  center_sq := center_sq0636
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0636.1
  jac_ok := checks0636.2.1
  accepted := checks0636.2.2

def tau0637 : RatBall :=
  ⟨⟨31/160, -41/160⟩, 3/320⟩
def center0637 : GaussianRat :=
  ⟨8852011/62500000, -87111573/500000000⟩
def contact0637 : RatBall := localContactBall tau0637 center0637
def work0637 : RoundedTauEval :=
  evalTau precision tau0637 contact0637 logTwoBall

theorem center_sq0637 : (center0637.re : ℝ)^2 +
    (center0637.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0637]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0637 : work0637.theta.ok = true ∧
    work0637.jac.invOK = true ∧ acceptsUnitSq work0637.out = true := by decide +kernel

def cell0637 : CellCertificate where
  tauBall := tau0637
  contactCenter := center0637
  contactBall := contact0637
  work := work0637
  center_sq := center_sq0637
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0637.1
  jac_ok := checks0637.2.1
  accepted := checks0637.2.2

def tau0638 : RatBall :=
  ⟨⟨5/32, -39/160⟩, 3/320⟩
def center0638 : GaussianRat :=
  ⟨57074691/500000000, -83923163/500000000⟩
def contact0638 : RatBall := localContactBall tau0638 center0638
def work0638 : RoundedTauEval :=
  evalTau precision tau0638 contact0638 logTwoBall

theorem center_sq0638 : (center0638.re : ℝ)^2 +
    (center0638.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0638]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0638 : work0638.theta.ok = true ∧
    work0638.jac.invOK = true ∧ acceptsUnitSq work0638.out = true := by decide +kernel

def cell0638 : CellCertificate where
  tauBall := tau0638
  contactCenter := center0638
  contactBall := contact0638
  work := work0638
  center_sq := center_sq0638
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0638.1
  jac_ok := checks0638.2.1
  accepted := checks0638.2.2

def tau0639 : RatBall :=
  ⟨⟨27/160, -39/160⟩, 3/320⟩
def center0639 : GaussianRat :=
  ⟨123057717/1000000000, -167087407/1000000000⟩
def contact0639 : RatBall := localContactBall tau0639 center0639
def work0639 : RoundedTauEval :=
  evalTau precision tau0639 contact0639 logTwoBall

theorem center_sq0639 : (center0639.re : ℝ)^2 +
    (center0639.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0639]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0639 : work0639.theta.ok = true ∧
    work0639.jac.invOK = true ∧ acceptsUnitSq work0639.out = true := by decide +kernel

def cell0639 : CellCertificate where
  tauBall := tau0639
  contactCenter := center0639
  contactBall := contact0639
  work := work0639
  center_sq := center_sq0639
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0639.1
  jac_ok := checks0639.2.1
  accepted := checks0639.2.2

def cells : List CellCertificate := [cell0632, cell0633, cell0634, cell0635, cell0636, cell0637, cell0638, cell0639]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0079

end


