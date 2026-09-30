-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0213_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0213_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:16:55.050769+00:00
-- url     : https://prove2.me/theorems/f4885dd7-0359-4e1c-8b34-94dcd53ac750
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0213 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0213 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0213 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0213 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0213 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0213

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1704 : RatBall :=
  ⟨⟨63/320, -109/320⟩, 3/640⟩
def center1704 : GaussianRat :=
  ⟨75841877/500000000, -234745077/1000000000⟩
def contact1704 : RatBall := localContactBall tau1704 center1704
def work1704 : RoundedTauEval :=
  evalTau precision tau1704 contact1704 logTwoBall

theorem center_sq1704 : (center1704.re : ℝ)^2 +
    (center1704.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1704]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1704 : work1704.theta.ok = true ∧
    work1704.jac.invOK = true ∧ acceptsUnitSq work1704.out = true := by decide +kernel

def cell1704 : CellCertificate where
  tauBall := tau1704
  contactCenter := center1704
  contactBall := contact1704
  work := work1704
  center_sq := center_sq1704
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1704.1
  jac_ok := checks1704.2.1
  accepted := checks1704.2.2

def tau1705 : RatBall :=
  ⟨⟨57/320, -107/320⟩, 3/640⟩
def center1705 : GaussianRat :=
  ⟨6857441/50000000, -46420737/200000000⟩
def contact1705 : RatBall := localContactBall tau1705 center1705
def work1705 : RoundedTauEval :=
  evalTau precision tau1705 contact1705 logTwoBall

theorem center_sq1705 : (center1705.re : ℝ)^2 +
    (center1705.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1705]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1705 : work1705.theta.ok = true ∧
    work1705.jac.invOK = true ∧ acceptsUnitSq work1705.out = true := by decide +kernel

def cell1705 : CellCertificate where
  tauBall := tau1705
  contactCenter := center1705
  contactBall := contact1705
  work := work1705
  center_sq := center_sq1705
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1705.1
  jac_ok := checks1705.2.1
  accepted := checks1705.2.2

def tau1706 : RatBall :=
  ⟨⟨59/320, -107/320⟩, 3/640⟩
def center1706 : GaussianRat :=
  ⟨141782257/1000000000, -231469249/1000000000⟩
def contact1706 : RatBall := localContactBall tau1706 center1706
def work1706 : RoundedTauEval :=
  evalTau precision tau1706 contact1706 logTwoBall

theorem center_sq1706 : (center1706.re : ℝ)^2 +
    (center1706.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1706]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1706 : work1706.theta.ok = true ∧
    work1706.jac.invOK = true ∧ acceptsUnitSq work1706.out = true := by decide +kernel

def cell1706 : CellCertificate where
  tauBall := tau1706
  contactCenter := center1706
  contactBall := contact1706
  work := work1706
  center_sq := center_sq1706
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1706.1
  jac_ok := checks1706.2.1
  accepted := checks1706.2.2

def tau1707 : RatBall :=
  ⟨⟨57/320, -21/64⟩, 3/640⟩
def center1707 : GaussianRat :=
  ⟨136531833/1000000000, -227470663/1000000000⟩
def contact1707 : RatBall := localContactBall tau1707 center1707
def work1707 : RoundedTauEval :=
  evalTau precision tau1707 contact1707 logTwoBall

theorem center_sq1707 : (center1707.re : ℝ)^2 +
    (center1707.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1707]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1707 : work1707.theta.ok = true ∧
    work1707.jac.invOK = true ∧ acceptsUnitSq work1707.out = true := by decide +kernel

def cell1707 : CellCertificate where
  tauBall := tau1707
  contactCenter := center1707
  contactBall := contact1707
  work := work1707
  center_sq := center_sq1707
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1707.1
  jac_ok := checks1707.2.1
  accepted := checks1707.2.2

def tau1708 : RatBall :=
  ⟨⟨59/320, -21/64⟩, 3/640⟩
def center1708 : GaussianRat :=
  ⟨70573769/500000000, -113426637/500000000⟩
def contact1708 : RatBall := localContactBall tau1708 center1708
def work1708 : RoundedTauEval :=
  evalTau precision tau1708 contact1708 logTwoBall

theorem center_sq1708 : (center1708.re : ℝ)^2 +
    (center1708.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1708]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1708 : work1708.theta.ok = true ∧
    work1708.jac.invOK = true ∧ acceptsUnitSq work1708.out = true := by decide +kernel

def cell1708 : CellCertificate where
  tauBall := tau1708
  contactCenter := center1708
  contactBall := contact1708
  work := work1708
  center_sq := center_sq1708
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1708.1
  jac_ok := checks1708.2.1
  accepted := checks1708.2.2

def tau1709 : RatBall :=
  ⟨⟨61/320, -107/320⟩, 3/640⟩
def center1709 : GaussianRat :=
  ⟨146398251/1000000000, -115408523/500000000⟩
def contact1709 : RatBall := localContactBall tau1709 center1709
def work1709 : RoundedTauEval :=
  evalTau precision tau1709 contact1709 logTwoBall

theorem center_sq1709 : (center1709.re : ℝ)^2 +
    (center1709.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1709]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1709 : work1709.theta.ok = true ∧
    work1709.jac.invOK = true ∧ acceptsUnitSq work1709.out = true := by decide +kernel

def cell1709 : CellCertificate where
  tauBall := tau1709
  contactCenter := center1709
  contactBall := contact1709
  work := work1709
  center_sq := center_sq1709
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1709.1
  jac_ok := checks1709.2.1
  accepted := checks1709.2.2

def tau1710 : RatBall :=
  ⟨⟨63/320, -107/320⟩, 3/640⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0213


