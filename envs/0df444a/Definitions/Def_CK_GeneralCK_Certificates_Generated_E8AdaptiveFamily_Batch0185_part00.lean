-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0185_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0185_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:22:38.213516+00:00
-- url     : https://prove2.me/theorems/a90126fa-a6f8-4e3a-844c-b400b056cb35
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0185 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1480 : RatBall :=
  ⟨⟨-21/320, -23/64⟩, 3/640⟩
def center1480 : GaussianRat :=
  ⟨-6547631/125000000, -64938653/250000000⟩
def contact1480 : RatBall := localContactBall tau1480 center1480
def work1480 : RoundedTauEval :=
  evalTau precision tau1480 contact1480 logTwoBall

theorem center_sq1480 : (center1480.re : ℝ)^2 +
    (center1480.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1480]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1480 : work1480.theta.ok = true ∧
    work1480.jac.invOK = true ∧ acceptsUnitSq work1480.out = true := by decide +kernel

def cell1480 : CellCertificate where
  tauBall := tau1480
  contactCenter := center1480
  contactBall := contact1480
  work := work1480
  center_sq := center_sq1480
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1480.1
  jac_ok := checks1480.2.1
  accepted := checks1480.2.2

def tau1481 : RatBall :=
  ⟨⟨-23/320, -113/320⟩, 3/640⟩
def center1481 : GaussianRat :=
  ⟨-57038551/1000000000, -63630699/250000000⟩
def contact1481 : RatBall := localContactBall tau1481 center1481
def work1481 : RoundedTauEval :=
  evalTau precision tau1481 contact1481 logTwoBall

theorem center_sq1481 : (center1481.re : ℝ)^2 +
    (center1481.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1481]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1481 : work1481.theta.ok = true ∧
    work1481.jac.invOK = true ∧ acceptsUnitSq work1481.out = true := by decide +kernel

def cell1481 : CellCertificate where
  tauBall := tau1481
  contactCenter := center1481
  contactBall := contact1481
  work := work1481
  center_sq := center_sq1481
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1481.1
  jac_ok := checks1481.2.1
  accepted := checks1481.2.2

def tau1482 : RatBall :=
  ⟨⟨-21/320, -113/320⟩, 3/640⟩
def center1482 : GaussianRat :=
  ⟨-13026633/250000000, -254806033/1000000000⟩
def contact1482 : RatBall := localContactBall tau1482 center1482
def work1482 : RoundedTauEval :=
  evalTau precision tau1482 contact1482 logTwoBall

theorem center_sq1482 : (center1482.re : ℝ)^2 +
    (center1482.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1482]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1482 : work1482.theta.ok = true ∧
    work1482.jac.invOK = true ∧ acceptsUnitSq work1482.out = true := by decide +kernel

def cell1482 : CellCertificate where
  tauBall := tau1482
  contactCenter := center1482
  contactBall := contact1482
  work := work1482
  center_sq := center_sq1482
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1482.1
  jac_ok := checks1482.2.1
  accepted := checks1482.2.2

def tau1483 : RatBall :=
  ⟨⟨-19/320, -23/64⟩, 3/640⟩
def center1483 : GaussianRat :=
  ⟨-47415929/1000000000, -260020027/1000000000⟩
def contact1483 : RatBall := localContactBall tau1483 center1483
def work1483 : RoundedTauEval :=
  evalTau precision tau1483 contact1483 logTwoBall

theorem center_sq1483 : (center1483.re : ℝ)^2 +
    (center1483.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1483]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1483 : work1483.theta.ok = true ∧
    work1483.jac.invOK = true ∧ acceptsUnitSq work1483.out = true := by decide +kernel

def cell1483 : CellCertificate where
  tauBall := tau1483
  contactCenter := center1483
  contactBall := contact1483
  work := work1483
  center_sq := center_sq1483
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1483.1
  jac_ok := checks1483.2.1
  accepted := checks1483.2.2

def tau1484 : RatBall :=
  ⟨⟨-17/320, -23/64⟩, 3/640⟩
def center1484 : GaussianRat :=
  ⟨-5305473/125000000, -65064861/250000000⟩
def contact1484 : RatBall := localContactBall tau1484 center1484
def work1484 : RoundedTauEval :=
  evalTau precision tau1484 contact1484 logTwoBall

theorem center_sq1484 : (center1484.re : ℝ)^2 +
    (center1484.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1484]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1484 : work1484.theta.ok = true ∧
    work1484.jac.invOK = true ∧ acceptsUnitSq work1484.out = true := by decide +kernel

def cell1484 : CellCertificate where
  tauBall := tau1484
  contactCenter := center1484
  contactBall := contact1484
  work := work1484
  center_sq := center_sq1484
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1484.1
  jac_ok := checks1484.2.1
  accepted := checks1484.2.2

def tau1485 : RatBall :=
  ⟨⟨-19/320, -113/320⟩, 3/640⟩
def center1485 : GaussianRat :=
  ⟨-47166967/1000000000, -255064157/1000000000⟩
def contact1485 : RatBall := localContactBall tau1485 center1485
def work1485 : RoundedTauEval :=
  evalTau precision tau1485 contact1485 logTwoBall

theorem center_sq1485 : (center1485.re : ℝ)^2 +
    (center1485.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1485]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1485 : work1485.theta.ok = true ∧
    work1485.jac.invOK = true ∧ acceptsUnitSq work1485.out = true := by decide +kernel

def cell1485 : CellCertificate where
  tauBall := tau1485
  contactCenter := center1485
  contactBall := contact1485
  work := work1485
  center_sq := center_sq1485
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1485.1
  jac_ok := checks1485.2.1
  accepted := checks1485.2.2

def tau1486 : RatBall :=
  ⟨⟨-17/320, -113/320⟩, 3/640⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185


