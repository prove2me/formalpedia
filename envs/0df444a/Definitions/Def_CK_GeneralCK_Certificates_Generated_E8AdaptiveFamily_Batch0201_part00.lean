-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0201_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0201_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:02:58.614015+00:00
-- url     : https://prove2.me/theorems/e9bbb2f8-8366-4760-a5da-bbd0f18d6f5b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0201 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0201 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0201 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0201 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0201 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0201

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1608 : RatBall :=
  ⟨⟨31/320, -117/320⟩, 3/640⟩
def center1608 : GaussianRat :=
  ⟨774869/10000000, -65742793/250000000⟩
def contact1608 : RatBall := localContactBall tau1608 center1608
def work1608 : RoundedTauEval :=
  evalTau precision tau1608 contact1608 logTwoBall

theorem center_sq1608 : (center1608.re : ℝ)^2 +
    (center1608.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1608]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1608 : work1608.theta.ok = true ∧
    work1608.jac.invOK = true ∧ acceptsUnitSq work1608.out = true := by decide +kernel

def cell1608 : CellCertificate where
  tauBall := tau1608
  contactCenter := center1608
  contactBall := contact1608
  work := work1608
  center_sq := center_sq1608
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1608.1
  jac_ok := checks1608.2.1
  accepted := checks1608.2.2

def tau1609 : RatBall :=
  ⟨⟨5/64, -23/64⟩, 3/640⟩
def center1609 : GaussianRat :=
  ⟨15571843/250000000, -51829311/200000000⟩
def contact1609 : RatBall := localContactBall tau1609 center1609
def work1609 : RoundedTauEval :=
  evalTau precision tau1609 contact1609 logTwoBall

theorem center_sq1609 : (center1609.re : ℝ)^2 +
    (center1609.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1609]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1609 : work1609.theta.ok = true ∧
    work1609.jac.invOK = true ∧ acceptsUnitSq work1609.out = true := by decide +kernel

def cell1609 : CellCertificate where
  tauBall := tau1609
  contactCenter := center1609
  contactBall := contact1609
  work := work1609
  center_sq := center_sq1609
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1609.1
  jac_ok := checks1609.2.1
  accepted := checks1609.2.2

def tau1610 : RatBall :=
  ⟨⟨27/320, -23/64⟩, 3/640⟩
def center1610 : GaussianRat :=
  ⟨67227179/1000000000, -258804339/1000000000⟩
def contact1610 : RatBall := localContactBall tau1610 center1610
def work1610 : RoundedTauEval :=
  evalTau precision tau1610 contact1610 logTwoBall

theorem center_sq1610 : (center1610.re : ℝ)^2 +
    (center1610.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1610]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1610 : work1610.theta.ok = true ∧
    work1610.jac.invOK = true ∧ acceptsUnitSq work1610.out = true := by decide +kernel

def cell1610 : CellCertificate where
  tauBall := tau1610
  contactCenter := center1610
  contactBall := contact1610
  work := work1610
  center_sq := center_sq1610
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1610.1
  jac_ok := checks1610.2.1
  accepted := checks1610.2.2

def tau1611 : RatBall :=
  ⟨⟨5/64, -113/320⟩, 3/640⟩
def center1611 : GaussianRat :=
  ⟨61962339/1000000000, -63553661/250000000⟩
def contact1611 : RatBall := localContactBall tau1611 center1611
def work1611 : RoundedTauEval :=
  evalTau precision tau1611 contact1611 logTwoBall

theorem center_sq1611 : (center1611.re : ℝ)^2 +
    (center1611.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1611]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1611 : work1611.theta.ok = true ∧
    work1611.jac.invOK = true ∧ acceptsUnitSq work1611.out = true := by decide +kernel

def cell1611 : CellCertificate where
  tauBall := tau1611
  contactCenter := center1611
  contactBall := contact1611
  work := work1611
  center_sq := center_sq1611
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1611.1
  jac_ok := checks1611.2.1
  accepted := checks1611.2.2

def tau1612 : RatBall :=
  ⟨⟨27/320, -113/320⟩, 3/640⟩
def center1612 : GaussianRat :=
  ⟨33438609/500000000, -253881789/1000000000⟩
def contact1612 : RatBall := localContactBall tau1612 center1612
def work1612 : RoundedTauEval :=
  evalTau precision tau1612 contact1612 logTwoBall

theorem center_sq1612 : (center1612.re : ℝ)^2 +
    (center1612.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1612]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1612 : work1612.theta.ok = true ∧
    work1612.jac.invOK = true ∧ acceptsUnitSq work1612.out = true := by decide +kernel

def cell1612 : CellCertificate where
  tauBall := tau1612
  contactCenter := center1612
  contactBall := contact1612
  work := work1612
  center_sq := center_sq1612
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1612.1
  jac_ok := checks1612.2.1
  accepted := checks1612.2.2

def tau1613 : RatBall :=
  ⟨⟨29/320, -23/64⟩, 3/640⟩
def center1613 : GaussianRat :=
  ⟨4509823/62500000, -258436977/1000000000⟩
def contact1613 : RatBall := localContactBall tau1613 center1613
def work1613 : RoundedTauEval :=
  evalTau precision tau1613 contact1613 logTwoBall

theorem center_sq1613 : (center1613.re : ℝ)^2 +
    (center1613.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1613]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1613 : work1613.theta.ok = true ∧
    work1613.jac.invOK = true ∧ acceptsUnitSq work1613.out = true := by decide +kernel

def cell1613 : CellCertificate where
  tauBall := tau1613
  contactCenter := center1613
  contactBall := contact1613
  work := work1613
  center_sq := center_sq1613
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1613.1
  jac_ok := checks1613.2.1
  accepted := checks1613.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0201


