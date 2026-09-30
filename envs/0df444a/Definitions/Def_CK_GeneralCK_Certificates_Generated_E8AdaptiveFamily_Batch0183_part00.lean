-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0183_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0183_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:37:55.590202+00:00
-- url     : https://prove2.me/theorems/71ec586e-9d72-42b6-9a4e-8c574daf65f9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0183 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1464 : RatBall :=
  ⟨⟨-29/320, -23/64⟩, 3/640⟩
def center1464 : GaussianRat :=
  ⟨-4509823/62500000, -258436977/1000000000⟩
def contact1464 : RatBall := localContactBall tau1464 center1464
def work1464 : RoundedTauEval :=
  evalTau precision tau1464 contact1464 logTwoBall

theorem center_sq1464 : (center1464.re : ℝ)^2 +
    (center1464.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1464]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1464 : work1464.theta.ok = true ∧
    work1464.jac.invOK = true ∧ acceptsUnitSq work1464.out = true := by decide +kernel

def cell1464 : CellCertificate where
  tauBall := tau1464
  contactCenter := center1464
  contactBall := contact1464
  work := work1464
  center_sq := center_sq1464
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1464.1
  jac_ok := checks1464.2.1
  accepted := checks1464.2.2

def tau1465 : RatBall :=
  ⟨⟨-31/320, -113/320⟩, 3/640⟩
def center1465 : GaussianRat :=
  ⟨-15335517/200000000, -253142899/1000000000⟩
def contact1465 : RatBall := localContactBall tau1465 center1465
def work1465 : RoundedTauEval :=
  evalTau precision tau1465 contact1465 logTwoBall

theorem center_sq1465 : (center1465.re : ℝ)^2 +
    (center1465.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1465]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1465 : work1465.theta.ok = true ∧
    work1465.jac.invOK = true ∧ acceptsUnitSq work1465.out = true := by decide +kernel

def cell1465 : CellCertificate where
  tauBall := tau1465
  contactCenter := center1465
  contactBall := contact1465
  work := work1465
  center_sq := center_sq1465
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1465.1
  jac_ok := checks1465.2.1
  accepted := checks1465.2.2

def tau1466 : RatBall :=
  ⟨⟨-29/320, -113/320⟩, 3/640⟩
def center1466 : GaussianRat :=
  ⟨-1794563/25000000, -253524459/1000000000⟩
def contact1466 : RatBall := localContactBall tau1466 center1466
def work1466 : RoundedTauEval :=
  evalTau precision tau1466 contact1466 logTwoBall

theorem center_sq1466 : (center1466.re : ℝ)^2 +
    (center1466.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1466]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1466 : work1466.theta.ok = true ∧
    work1466.jac.invOK = true ∧ acceptsUnitSq work1466.out = true := by decide +kernel

def cell1466 : CellCertificate where
  tauBall := tau1466
  contactCenter := center1466
  contactBall := contact1466
  work := work1466
  center_sq := center_sq1466
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1466.1
  jac_ok := checks1466.2.1
  accepted := checks1466.2.2

def tau1467 : RatBall :=
  ⟨⟨-27/320, -23/64⟩, 3/640⟩
def center1467 : GaussianRat :=
  ⟨-67227179/1000000000, -258804339/1000000000⟩
def contact1467 : RatBall := localContactBall tau1467 center1467
def work1467 : RoundedTauEval :=
  evalTau precision tau1467 contact1467 logTwoBall

theorem center_sq1467 : (center1467.re : ℝ)^2 +
    (center1467.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1467]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1467 : work1467.theta.ok = true ∧
    work1467.jac.invOK = true ∧ acceptsUnitSq work1467.out = true := by decide +kernel

def cell1467 : CellCertificate where
  tauBall := tau1467
  contactCenter := center1467
  contactBall := contact1467
  work := work1467
  center_sq := center_sq1467
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1467.1
  jac_ok := checks1467.2.1
  accepted := checks1467.2.2

def tau1468 : RatBall :=
  ⟨⟨-5/64, -23/64⟩, 3/640⟩
def center1468 : GaussianRat :=
  ⟨-15571843/250000000, -51829311/200000000⟩
def contact1468 : RatBall := localContactBall tau1468 center1468
def work1468 : RoundedTauEval :=
  evalTau precision tau1468 contact1468 logTwoBall

theorem center_sq1468 : (center1468.re : ℝ)^2 +
    (center1468.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1468]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1468 : work1468.theta.ok = true ∧
    work1468.jac.invOK = true ∧ acceptsUnitSq work1468.out = true := by decide +kernel

def cell1468 : CellCertificate where
  tauBall := tau1468
  contactCenter := center1468
  contactBall := contact1468
  work := work1468
  center_sq := center_sq1468
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1468.1
  jac_ok := checks1468.2.1
  accepted := checks1468.2.2

def tau1469 : RatBall :=
  ⟨⟨-27/320, -113/320⟩, 3/640⟩
def center1469 : GaussianRat :=
  ⟨-33438609/500000000, -253881789/1000000000⟩
def contact1469 : RatBall := localContactBall tau1469 center1469
def work1469 : RoundedTauEval :=
  evalTau precision tau1469 contact1469 logTwoBall

theorem center_sq1469 : (center1469.re : ℝ)^2 +
    (center1469.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1469]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1469 : work1469.theta.ok = true ∧
    work1469.jac.invOK = true ∧ acceptsUnitSq work1469.out = true := by decide +kernel

def cell1469 : CellCertificate where
  tauBall := tau1469
  contactCenter := center1469
  contactBall := contact1469
  work := work1469
  center_sq := center_sq1469
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1469.1
  jac_ok := checks1469.2.1
  accepted := checks1469.2.2

def tau1470 : RatBall :=
  ⟨⟨-5/64, -113/320⟩, 3/640⟩
def center1470 : GaussianRat :=
  ⟨-61962339/1000000000, -63553661/250000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183


