-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0084
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0084
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:37:32.161533+00:00
-- url     : https://prove2.me/theorems/41f8e076-3c10-4983-b039-4fbe49008608
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0084` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0084` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0084` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0084 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0084.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0084 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0084

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0672 : RatBall :=
  ⟨⟨37/160, -33/160⟩, 3/320⟩
def center0672 : GaussianRat :=
  ⟨164030831/1000000000, -3423667/25000000⟩
def contact0672 : RatBall := localContactBall tau0672 center0672
def work0672 : RoundedTauEval :=
  evalTau precision tau0672 contact0672 logTwoBall

theorem center_sq0672 : (center0672.re : ℝ)^2 +
    (center0672.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0672]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0672 : work0672.theta.ok = true ∧
    work0672.jac.invOK = true ∧ acceptsUnitSq work0672.out = true := by decide +kernel

def cell0672 : CellCertificate where
  tauBall := tau0672
  contactCenter := center0672
  contactBall := contact0672
  work := work0672
  center_sq := center_sq0672
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0672.1
  jac_ok := checks0672.2.1
  accepted := checks0672.2.2

def tau0673 : RatBall :=
  ⟨⟨39/160, -33/160⟩, 3/320⟩
def center0673 : GaussianRat :=
  ⟨172488051/1000000000, -136096987/1000000000⟩
def contact0673 : RatBall := localContactBall tau0673 center0673
def work0673 : RoundedTauEval :=
  evalTau precision tau0673 contact0673 logTwoBall

theorem center_sq0673 : (center0673.re : ℝ)^2 +
    (center0673.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0673]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0673 : work0673.theta.ok = true ∧
    work0673.jac.invOK = true ∧ acceptsUnitSq work0673.out = true := by decide +kernel

def cell0673 : CellCertificate where
  tauBall := tau0673
  contactCenter := center0673
  contactBall := contact0673
  work := work0673
  center_sq := center_sq0673
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0673.1
  jac_ok := checks0673.2.1
  accepted := checks0673.2.2

def tau0674 : RatBall :=
  ⟨⟨41/160, -39/160⟩, 3/320⟩
def center0674 : GaussianRat :=
  ⟨91934683/500000000, -80231659/500000000⟩
def contact0674 : RatBall := localContactBall tau0674 center0674
def work0674 : RoundedTauEval :=
  evalTau precision tau0674 contact0674 logTwoBall

theorem center_sq0674 : (center0674.re : ℝ)^2 +
    (center0674.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0674]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0674 : work0674.theta.ok = true ∧
    work0674.jac.invOK = true ∧ acceptsUnitSq work0674.out = true := by decide +kernel

def cell0674 : CellCertificate where
  tauBall := tau0674
  contactCenter := center0674
  contactBall := contact0674
  work := work0674
  center_sq := center_sq0674
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0674.1
  jac_ok := checks0674.2.1
  accepted := checks0674.2.2

def tau0675 : RatBall :=
  ⟨⟨43/160, -39/160⟩, 3/320⟩
def center0675 : GaussianRat :=
  ⟨96152483/500000000, -159351351/1000000000⟩
def contact0675 : RatBall := localContactBall tau0675 center0675
def work0675 : RoundedTauEval :=
  evalTau precision tau0675 contact0675 logTwoBall

theorem center_sq0675 : (center0675.re : ℝ)^2 +
    (center0675.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0675]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0675 : work0675.theta.ok = true ∧
    work0675.jac.invOK = true ∧ acceptsUnitSq work0675.out = true := by decide +kernel

def cell0675 : CellCertificate where
  tauBall := tau0675
  contactCenter := center0675
  contactBall := contact0675
  work := work0675
  center_sq := center_sq0675
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0675.1
  jac_ok := checks0675.2.1
  accepted := checks0675.2.2

def tau0676 : RatBall :=
  ⟨⟨41/160, -37/160⟩, 3/320⟩
def center0676 : GaussianRat :=
  ⟨182809387/1000000000, -76006029/500000000⟩
def contact0676 : RatBall := localContactBall tau0676 center0676
def work0676 : RoundedTauEval :=
  evalTau precision tau0676 contact0676 logTwoBall

theorem center_sq0676 : (center0676.re : ℝ)^2 +
    (center0676.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0676]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0676 : work0676.theta.ok = true ∧
    work0676.jac.invOK = true ∧ acceptsUnitSq work0676.out = true := by decide +kernel

def cell0676 : CellCertificate where
  tauBall := tau0676
  contactCenter := center0676
  contactBall := contact0676
  work := work0676
  center_sq := center_sq0676
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0676.1
  jac_ok := checks0676.2.1
  accepted := checks0676.2.2

def tau0677 : RatBall :=
  ⟨⟨43/160, -37/160⟩, 3/320⟩
def center0677 : GaussianRat :=
  ⟨191209303/1000000000, -1887097/12500000⟩
def contact0677 : RatBall := localContactBall tau0677 center0677
def work0677 : RoundedTauEval :=
  evalTau precision tau0677 contact0677 logTwoBall

theorem center_sq0677 : (center0677.re : ℝ)^2 +
    (center0677.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0677]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0677 : work0677.theta.ok = true ∧
    work0677.jac.invOK = true ∧ acceptsUnitSq work0677.out = true := by decide +kernel

def cell0677 : CellCertificate where
  tauBall := tau0677
  contactCenter := center0677
  contactBall := contact0677
  work := work0677
  center_sq := center_sq0677
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0677.1
  jac_ok := checks0677.2.1
  accepted := checks0677.2.2

def tau0678 : RatBall :=
  ⟨⟨9/32, -39/160⟩, 3/320⟩
def center0678 : GaussianRat :=
  ⟨200670971/1000000000, -79101837/500000000⟩
def contact0678 : RatBall := localContactBall tau0678 center0678
def work0678 : RoundedTauEval :=
  evalTau precision tau0678 contact0678 logTwoBall

theorem center_sq0678 : (center0678.re : ℝ)^2 +
    (center0678.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0678]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0678 : work0678.theta.ok = true ∧
    work0678.jac.invOK = true ∧ acceptsUnitSq work0678.out = true := by decide +kernel

def cell0678 : CellCertificate where
  tauBall := tau0678
  contactCenter := center0678
  contactBall := contact0678
  work := work0678
  center_sq := center_sq0678
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0678.1
  jac_ok := checks0678.2.1
  accepted := checks0678.2.2

def tau0679 : RatBall :=
  ⟨⟨9/32, -37/160⟩, 3/320⟩
def center0679 : GaussianRat :=
  ⟨199541503/1000000000, -74944839/500000000⟩
def contact0679 : RatBall := localContactBall tau0679 center0679
def work0679 : RoundedTauEval :=
  evalTau precision tau0679 contact0679 logTwoBall

theorem center_sq0679 : (center0679.re : ℝ)^2 +
    (center0679.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0679]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0679 : work0679.theta.ok = true ∧
    work0679.jac.invOK = true ∧ acceptsUnitSq work0679.out = true := by decide +kernel

def cell0679 : CellCertificate where
  tauBall := tau0679
  contactCenter := center0679
  contactBall := contact0679
  work := work0679
  center_sq := center_sq0679
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0679.1
  jac_ok := checks0679.2.1
  accepted := checks0679.2.2

def cells : List CellCertificate := [cell0672, cell0673, cell0674, cell0675, cell0676, cell0677, cell0678, cell0679]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0084

end


