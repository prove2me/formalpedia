-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0217_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0217_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:19:59.272184+00:00
-- url     : https://prove2.me/theorems/8b673e2a-a0b2-4096-9ffa-9d0f6b7a08c0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0217 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0217_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell1739 : CellCertificate where
  tauBall := tau1739
  contactCenter := center1739
  contactBall := contact1739
  work := work1739
  center_sq := center_sq1739
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1739.1
  jac_ok := checks1739.2.1
  accepted := checks1739.2.2

def tau1740 : RatBall :=
  ⟨⟨67/320, -21/64⟩, 3/640⟩
def center1740 : GaussianRat :=
  ⟨79717703/500000000, -224213933/1000000000⟩
def contact1740 : RatBall := localContactBall tau1740 center1740
def work1740 : RoundedTauEval :=
  evalTau precision tau1740 contact1740 logTwoBall

theorem center_sq1740 : (center1740.re : ℝ)^2 +
    (center1740.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1740]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1740 : work1740.theta.ok = true ∧
    work1740.jac.invOK = true ∧ acceptsUnitSq work1740.out = true := by decide +kernel

def cell1740 : CellCertificate where
  tauBall := tau1740
  contactCenter := center1740
  contactBall := contact1740
  work := work1740
  center_sq := center_sq1740
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1740.1
  jac_ok := checks1740.2.1
  accepted := checks1740.2.2

def tau1741 : RatBall :=
  ⟨⟨69/320, -107/320⟩, 3/640⟩
def center1741 : GaussianRat :=
  ⟨20584937/125000000, -228038057/1000000000⟩
def contact1741 : RatBall := localContactBall tau1741 center1741
def work1741 : RoundedTauEval :=
  evalTau precision tau1741 contact1741 logTwoBall

theorem center_sq1741 : (center1741.re : ℝ)^2 +
    (center1741.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1741]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1741 : work1741.theta.ok = true ∧
    work1741.jac.invOK = true ∧ acceptsUnitSq work1741.out = true := by decide +kernel

def cell1741 : CellCertificate where
  tauBall := tau1741
  contactCenter := center1741
  contactBall := contact1741
  work := work1741
  center_sq := center_sq1741
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1741.1
  jac_ok := checks1741.2.1
  accepted := checks1741.2.2

def tau1742 : RatBall :=
  ⟨⟨69/320, -21/64⟩, 3/640⟩
def center1742 : GaussianRat :=
  ⟨81980819/500000000, -223513477/1000000000⟩
def contact1742 : RatBall := localContactBall tau1742 center1742
def work1742 : RoundedTauEval :=
  evalTau precision tau1742 contact1742 logTwoBall

theorem center_sq1742 : (center1742.re : ℝ)^2 +
    (center1742.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1742]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1742 : work1742.theta.ok = true ∧
    work1742.jac.invOK = true ∧ acceptsUnitSq work1742.out = true := by decide +kernel

def cell1742 : CellCertificate where
  tauBall := tau1742
  contactCenter := center1742
  contactBall := contact1742
  work := work1742
  center_sq := center_sq1742
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1742.1
  jac_ok := checks1742.2.1
  accepted := checks1742.2.2

def tau1743 : RatBall :=
  ⟨⟨71/320, -21/64⟩, 3/640⟩
def center1743 : GaussianRat :=
  ⟨168468823/1000000000, -55699379/250000000⟩
def contact1743 : RatBall := localContactBall tau1743 center1743
def work1743 : RoundedTauEval :=
  evalTau precision tau1743 contact1743 logTwoBall

theorem center_sq1743 : (center1743.re : ℝ)^2 +
    (center1743.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1743]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217


