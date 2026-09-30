-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0082
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0082
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:39:59.978785+00:00
-- url     : https://prove2.me/theorems/ec31e815-2571-4eb5-8549-cb8e4fe11c4f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0082` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0082` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0082` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0082 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0082.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0082 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0082

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0656 : RatBall :=
  ⟨⟨41/160, -41/160⟩, 3/320⟩
def center0656 : GaussianRat :=
  ⟨184996961/1000000000, -21119029/125000000⟩
def contact0656 : RatBall := localContactBall tau0656 center0656
def work0656 : RoundedTauEval :=
  evalTau precision tau0656 contact0656 logTwoBall

theorem center_sq0656 : (center0656.re : ℝ)^2 +
    (center0656.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0656]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0656 : work0656.theta.ok = true ∧
    work0656.jac.invOK = true ∧ acceptsUnitSq work0656.out = true := by decide +kernel

def cell0656 : CellCertificate where
  tauBall := tau0656
  contactCenter := center0656
  contactBall := contact0656
  work := work0656
  center_sq := center_sq0656
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0656.1
  jac_ok := checks0656.2.1
  accepted := checks0656.2.2

def tau0657 : RatBall :=
  ⟨⟨43/160, -41/160⟩, 3/320⟩
def center0657 : GaussianRat :=
  ⟨193470247/1000000000, -167770653/1000000000⟩
def contact0657 : RatBall := localContactBall tau0657 center0657
def work0657 : RoundedTauEval :=
  evalTau precision tau0657 contact0657 logTwoBall

theorem center_sq0657 : (center0657.re : ℝ)^2 +
    (center0657.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0657]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0657 : work0657.theta.ok = true ∧
    work0657.jac.invOK = true ∧ acceptsUnitSq work0657.out = true := by decide +kernel

def cell0657 : CellCertificate where
  tauBall := tau0657
  contactCenter := center0657
  contactBall := contact0657
  work := work0657
  center_sq := center_sq0657
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0657.1
  jac_ok := checks0657.2.1
  accepted := checks0657.2.2

def tau0658 : RatBall :=
  ⟨⟨33/160, -39/160⟩, 3/320⟩
def center0658 : GaussianRat :=
  ⟨18684153/125000000, -164515579/1000000000⟩
def contact0658 : RatBall := localContactBall tau0658 center0658
def work0658 : RoundedTauEval :=
  evalTau precision tau0658 contact0658 logTwoBall

theorem center_sq0658 : (center0658.re : ℝ)^2 +
    (center0658.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0658]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0658 : work0658.theta.ok = true ∧
    work0658.jac.invOK = true ∧ acceptsUnitSq work0658.out = true := by decide +kernel

def cell0658 : CellCertificate where
  tauBall := tau0658
  contactCenter := center0658
  contactBall := contact0658
  work := work0658
  center_sq := center_sq0658
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0658.1
  jac_ok := checks0658.2.1
  accepted := checks0658.2.2

def tau0659 : RatBall :=
  ⟨⟨7/32, -39/160⟩, 3/320⟩
def center0659 : GaussianRat :=
  ⟨9885359/62500000, -81782823/500000000⟩
def contact0659 : RatBall := localContactBall tau0659 center0659
def work0659 : RoundedTauEval :=
  evalTau precision tau0659 contact0659 logTwoBall

theorem center_sq0659 : (center0659.re : ℝ)^2 +
    (center0659.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0659]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0659 : work0659.theta.ok = true ∧
    work0659.jac.invOK = true ∧ acceptsUnitSq work0659.out = true := by decide +kernel

def cell0659 : CellCertificate where
  tauBall := tau0659
  contactCenter := center0659
  contactBall := contact0659
  work := work0659
  center_sq := center_sq0659
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0659.1
  jac_ok := checks0659.2.1
  accepted := checks0659.2.2

def tau0660 : RatBall :=
  ⟨⟨33/160, -37/160⟩, 3/320⟩
def center0660 : GaussianRat :=
  ⟨148574359/1000000000, -31163137/200000000⟩
def contact0660 : RatBall := localContactBall tau0660 center0660
def work0660 : RoundedTauEval :=
  evalTau precision tau0660 contact0660 logTwoBall

theorem center_sq0660 : (center0660.re : ℝ)^2 +
    (center0660.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0660]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0660 : work0660.theta.ok = true ∧
    work0660.jac.invOK = true ∧ acceptsUnitSq work0660.out = true := by decide +kernel

def cell0660 : CellCertificate where
  tauBall := tau0660
  contactCenter := center0660
  contactBall := contact0660
  work := work0660
  center_sq := center_sq0660
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0660.1
  jac_ok := checks0660.2.1
  accepted := checks0660.2.2

def tau0661 : RatBall :=
  ⟨⟨7/32, -37/160⟩, 3/320⟩
def center0661 : GaussianRat :=
  ⟨78611951/500000000, -154924327/1000000000⟩
def contact0661 : RatBall := localContactBall tau0661 center0661
def work0661 : RoundedTauEval :=
  evalTau precision tau0661 contact0661 logTwoBall

theorem center_sq0661 : (center0661.re : ℝ)^2 +
    (center0661.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0661]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0661 : work0661.theta.ok = true ∧
    work0661.jac.invOK = true ∧ acceptsUnitSq work0661.out = true := by decide +kernel

def cell0661 : CellCertificate where
  tauBall := tau0661
  contactCenter := center0661
  contactBall := contact0661
  work := work0661
  center_sq := center_sq0661
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0661.1
  jac_ok := checks0661.2.1
  accepted := checks0661.2.2

def tau0662 : RatBall :=
  ⟨⟨37/160, -39/160⟩, 3/320⟩
def center0662 : GaussianRat :=
  ⟨83398769/500000000, -20321547/125000000⟩
def contact0662 : RatBall := localContactBall tau0662 center0662
def work0662 : RoundedTauEval :=
  evalTau precision tau0662 contact0662 logTwoBall

theorem center_sq0662 : (center0662.re : ℝ)^2 +
    (center0662.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0662]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0662 : work0662.theta.ok = true ∧
    work0662.jac.invOK = true ∧ acceptsUnitSq work0662.out = true := by decide +kernel

def cell0662 : CellCertificate where
  tauBall := tau0662
  contactCenter := center0662
  contactBall := contact0662
  work := work0662
  center_sq := center_sq0662
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0662.1
  jac_ok := checks0662.2.1
  accepted := checks0662.2.2

def tau0663 : RatBall :=
  ⟨⟨39/160, -39/160⟩, 3/320⟩
def center0663 : GaussianRat :=
  ⟨7014647/40000000, -32307527/200000000⟩
def contact0663 : RatBall := localContactBall tau0663 center0663
def work0663 : RoundedTauEval :=
  evalTau precision tau0663 contact0663 logTwoBall

theorem center_sq0663 : (center0663.re : ℝ)^2 +
    (center0663.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0663]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0663 : work0663.theta.ok = true ∧
    work0663.jac.invOK = true ∧ acceptsUnitSq work0663.out = true := by decide +kernel

def cell0663 : CellCertificate where
  tauBall := tau0663
  contactCenter := center0663
  contactBall := contact0663
  work := work0663
  center_sq := center_sq0663
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0663.1
  jac_ok := checks0663.2.1
  accepted := checks0663.2.2

def cells : List CellCertificate := [cell0656, cell0657, cell0658, cell0659, cell0660, cell0661, cell0662, cell0663]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0082

end


