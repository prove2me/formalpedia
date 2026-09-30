-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0209
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0209
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:49:28.4897+00:00
-- url     : https://prove2.me/theorems/b57d183f-1949-425a-8f3a-c0f3a4f27182
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0209` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0209` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0209` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0209 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0209.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0209 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0209

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1672 : RatBall :=
  ⟨⟨43/320, -107/320⟩, 3/640⟩
def center1672 : GaussianRat :=
  ⟨104264923/1000000000, -236017459/1000000000⟩
def contact1672 : RatBall := localContactBall tau1672 center1672
def work1672 : RoundedTauEval :=
  evalTau precision tau1672 contact1672 logTwoBall

theorem center_sq1672 : (center1672.re : ℝ)^2 +
    (center1672.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1672]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1672 : work1672.theta.ok = true ∧
    work1672.jac.invOK = true ∧ acceptsUnitSq work1672.out = true := by decide +kernel

def cell1672 : CellCertificate where
  tauBall := tau1672
  contactCenter := center1672
  contactBall := contact1672
  work := work1672
  center_sq := center_sq1672
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1672.1
  jac_ok := checks1672.2.1
  accepted := checks1672.2.2

def tau1673 : RatBall :=
  ⟨⟨41/320, -21/64⟩, 3/640⟩
def center1673 : GaussianRat :=
  ⟨12380739/125000000, -115872433/500000000⟩
def contact1673 : RatBall := localContactBall tau1673 center1673
def work1673 : RoundedTauEval :=
  evalTau precision tau1673 contact1673 logTwoBall

theorem center_sq1673 : (center1673.re : ℝ)^2 +
    (center1673.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1673]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1673 : work1673.theta.ok = true ∧
    work1673.jac.invOK = true ∧ acceptsUnitSq work1673.out = true := by decide +kernel

def cell1673 : CellCertificate where
  tauBall := tau1673
  contactCenter := center1673
  contactBall := contact1673
  work := work1673
  center_sq := center_sq1673
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1673.1
  jac_ok := checks1673.2.1
  accepted := checks1673.2.2

def tau1674 : RatBall :=
  ⟨⟨43/320, -21/64⟩, 3/640⟩
def center1674 : GaussianRat :=
  ⟨103781603/1000000000, -28909781/125000000⟩
def contact1674 : RatBall := localContactBall tau1674 center1674
def work1674 : RoundedTauEval :=
  evalTau precision tau1674 contact1674 logTwoBall

theorem center_sq1674 : (center1674.re : ℝ)^2 +
    (center1674.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1674]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1674 : work1674.theta.ok = true ∧
    work1674.jac.invOK = true ∧ acceptsUnitSq work1674.out = true := by decide +kernel

def cell1674 : CellCertificate where
  tauBall := tau1674
  contactCenter := center1674
  contactBall := contact1674
  work := work1674
  center_sq := center_sq1674
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1674.1
  jac_ok := checks1674.2.1
  accepted := checks1674.2.2

def tau1675 : RatBall :=
  ⟨⟨9/64, -107/320⟩, 3/640⟩
def center1675 : GaussianRat :=
  ⟨109007417/1000000000, -235517221/1000000000⟩
def contact1675 : RatBall := localContactBall tau1675 center1675
def work1675 : RoundedTauEval :=
  evalTau precision tau1675 contact1675 logTwoBall

theorem center_sq1675 : (center1675.re : ℝ)^2 +
    (center1675.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1675]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1675 : work1675.theta.ok = true ∧
    work1675.jac.invOK = true ∧ acceptsUnitSq work1675.out = true := by decide +kernel

def cell1675 : CellCertificate where
  tauBall := tau1675
  contactCenter := center1675
  contactBall := contact1675
  work := work1675
  center_sq := center_sq1675
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1675.1
  jac_ok := checks1675.2.1
  accepted := checks1675.2.2

def tau1676 : RatBall :=
  ⟨⟨47/320, -107/320⟩, 3/640⟩
def center1676 : GaussianRat :=
  ⟨56867911/500000000, -234996813/1000000000⟩
def contact1676 : RatBall := localContactBall tau1676 center1676
def work1676 : RoundedTauEval :=
  evalTau precision tau1676 contact1676 logTwoBall

theorem center_sq1676 : (center1676.re : ℝ)^2 +
    (center1676.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1676]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1676 : work1676.theta.ok = true ∧
    work1676.jac.invOK = true ∧ acceptsUnitSq work1676.out = true := by decide +kernel

def cell1676 : CellCertificate where
  tauBall := tau1676
  contactCenter := center1676
  contactBall := contact1676
  work := work1676
  center_sq := center_sq1676
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1676.1
  jac_ok := checks1676.2.1
  accepted := checks1676.2.2

def tau1677 : RatBall :=
  ⟨⟨9/64, -21/64⟩, 3/640⟩
def center1677 : GaussianRat :=
  ⟨21700807/200000000, -115395841/500000000⟩
def contact1677 : RatBall := localContactBall tau1677 center1677
def work1677 : RoundedTauEval :=
  evalTau precision tau1677 contact1677 logTwoBall

theorem center_sq1677 : (center1677.re : ℝ)^2 +
    (center1677.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1677]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1677 : work1677.theta.ok = true ∧
    work1677.jac.invOK = true ∧ acceptsUnitSq work1677.out = true := by decide +kernel

def cell1677 : CellCertificate where
  tauBall := tau1677
  contactCenter := center1677
  contactBall := contact1677
  work := work1677
  center_sq := center_sq1677
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1677.1
  jac_ok := checks1677.2.1
  accepted := checks1677.2.2

def tau1678 : RatBall :=
  ⟨⟨47/320, -21/64⟩, 3/640⟩
def center1678 : GaussianRat :=
  ⟨22642537/200000000, -230285467/1000000000⟩
def contact1678 : RatBall := localContactBall tau1678 center1678
def work1678 : RoundedTauEval :=
  evalTau precision tau1678 contact1678 logTwoBall

theorem center_sq1678 : (center1678.re : ℝ)^2 +
    (center1678.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1678]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1678 : work1678.theta.ok = true ∧
    work1678.jac.invOK = true ∧ acceptsUnitSq work1678.out = true := by decide +kernel

def cell1678 : CellCertificate where
  tauBall := tau1678
  contactCenter := center1678
  contactBall := contact1678
  work := work1678
  center_sq := center_sq1678
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1678.1
  jac_ok := checks1678.2.1
  accepted := checks1678.2.2

def tau1679 : RatBall :=
  ⟨⟨9/64, -103/320⟩, 3/640⟩
def center1679 : GaussianRat :=
  ⟨21602887/200000000, -45217159/200000000⟩
def contact1679 : RatBall := localContactBall tau1679 center1679
def work1679 : RoundedTauEval :=
  evalTau precision tau1679 contact1679 logTwoBall

theorem center_sq1679 : (center1679.re : ℝ)^2 +
    (center1679.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1679]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1679 : work1679.theta.ok = true ∧
    work1679.jac.invOK = true ∧ acceptsUnitSq work1679.out = true := by decide +kernel

def cell1679 : CellCertificate where
  tauBall := tau1679
  contactCenter := center1679
  contactBall := contact1679
  work := work1679
  center_sq := center_sq1679
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1679.1
  jac_ok := checks1679.2.1
  accepted := checks1679.2.2

def cells : List CellCertificate := [cell1672, cell1673, cell1674, cell1675, cell1676, cell1677, cell1678, cell1679]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0209

end


