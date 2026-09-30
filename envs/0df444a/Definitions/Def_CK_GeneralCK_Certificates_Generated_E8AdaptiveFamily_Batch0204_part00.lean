-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0204_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0204_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:08:46.279545+00:00
-- url     : https://prove2.me/theorems/c5db8cb2-42fe-4922-852c-6803195c3c14
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0204 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1632 : RatBall :=
  ⟨⟨39/320, -117/320⟩, 3/640⟩
def center1632 : GaussianRat :=
  ⟨97144261/1000000000, -261108469/1000000000⟩
def contact1632 : RatBall := localContactBall tau1632 center1632
def work1632 : RoundedTauEval :=
  evalTau precision tau1632 contact1632 logTwoBall

theorem center_sq1632 : (center1632.re : ℝ)^2 +
    (center1632.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1632]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1632 : work1632.theta.ok = true ∧
    work1632.jac.invOK = true ∧ acceptsUnitSq work1632.out = true := by decide +kernel

def cell1632 : CellCertificate where
  tauBall := tau1632
  contactCenter := center1632
  contactBall := contact1632
  work := work1632
  center_sq := center_sq1632
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1632.1
  jac_ok := checks1632.2.1
  accepted := checks1632.2.2

def tau1633 : RatBall :=
  ⟨⟨33/320, -23/64⟩, 3/640⟩
def center1633 : GaussianRat :=
  ⟨40992501/500000000, -257627847/1000000000⟩
def contact1633 : RatBall := localContactBall tau1633 center1633
def work1633 : RoundedTauEval :=
  evalTau precision tau1633 contact1633 logTwoBall

theorem center_sq1633 : (center1633.re : ℝ)^2 +
    (center1633.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1633]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1633 : work1633.theta.ok = true ∧
    work1633.jac.invOK = true ∧ acceptsUnitSq work1633.out = true := by decide +kernel

def cell1633 : CellCertificate where
  tauBall := tau1633
  contactCenter := center1633
  contactBall := contact1633
  work := work1633
  center_sq := center_sq1633
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1633.1
  jac_ok := checks1633.2.1
  accepted := checks1633.2.2

def tau1634 : RatBall :=
  ⟨⟨7/64, -23/64⟩, 3/640⟩
def center1634 : GaussianRat :=
  ⟨43440767/500000000, -257186633/1000000000⟩
def contact1634 : RatBall := localContactBall tau1634 center1634
def work1634 : RoundedTauEval :=
  evalTau precision tau1634 contact1634 logTwoBall

theorem center_sq1634 : (center1634.re : ℝ)^2 +
    (center1634.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1634]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1634 : work1634.theta.ok = true ∧
    work1634.jac.invOK = true ∧ acceptsUnitSq work1634.out = true := by decide +kernel

def cell1634 : CellCertificate where
  tauBall := tau1634
  contactCenter := center1634
  contactBall := contact1634
  work := work1634
  center_sq := center_sq1634
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1634.1
  jac_ok := checks1634.2.1
  accepted := checks1634.2.2

def tau1635 : RatBall :=
  ⟨⟨33/320, -113/320⟩, 3/640⟩
def center1635 : GaussianRat :=
  ⟨16312353/200000000, -252737367/1000000000⟩
def contact1635 : RatBall := localContactBall tau1635 center1635
def work1635 : RoundedTauEval :=
  evalTau precision tau1635 contact1635 logTwoBall

theorem center_sq1635 : (center1635.re : ℝ)^2 +
    (center1635.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1635]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1635 : work1635.theta.ok = true ∧
    work1635.jac.invOK = true ∧ acceptsUnitSq work1635.out = true := by decide +kernel

def cell1635 : CellCertificate where
  tauBall := tau1635
  contactCenter := center1635
  contactBall := contact1635
  work := work1635
  center_sq := center_sq1635
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1635.1
  jac_ok := checks1635.2.1
  accepted := checks1635.2.2

def tau1636 : RatBall :=
  ⟨⟨7/64, -113/320⟩, 3/640⟩
def center1636 : GaussianRat :=
  ⟨86434423/1000000000, -50461627/200000000⟩
def contact1636 : RatBall := localContactBall tau1636 center1636
def work1636 : RoundedTauEval :=
  evalTau precision tau1636 contact1636 logTwoBall

theorem center_sq1636 : (center1636.re : ℝ)^2 +
    (center1636.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1636]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1636 : work1636.theta.ok = true ∧
    work1636.jac.invOK = true ∧ acceptsUnitSq work1636.out = true := by decide +kernel

def cell1636 : CellCertificate where
  tauBall := tau1636
  contactCenter := center1636
  contactBall := contact1636
  work := work1636
  center_sq := center_sq1636
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1636.1
  jac_ok := checks1636.2.1
  accepted := checks1636.2.2

def tau1637 : RatBall :=
  ⟨⟨37/320, -23/64⟩, 3/640⟩
def center1637 : GaussianRat :=
  ⟨91765617/1000000000, -12836069/50000000⟩
def contact1637 : RatBall := localContactBall tau1637 center1637
def work1637 : RoundedTauEval :=
  evalTau precision tau1637 contact1637 logTwoBall

theorem center_sq1637 : (center1637.re : ℝ)^2 +
    (center1637.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1637]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1637 : work1637.theta.ok = true ∧
    work1637.jac.invOK = true ∧ acceptsUnitSq work1637.out = true := by decide +kernel

def cell1637 : CellCertificate where
  tauBall := tau1637
  contactCenter := center1637
  contactBall := contact1637
  work := work1637
  center_sq := center_sq1637
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1637.1
  jac_ok := checks1637.2.1
  accepted := checks1637.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204


