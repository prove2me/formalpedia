-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0188
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0188
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:04:29.925497+00:00
-- url     : https://prove2.me/theorems/7261ef23-212b-4d2e-a6c9-be8b5ebc26fa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0188.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0188_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1509 : (center1509.re : ℝ)^2 +
    (center1509.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1509]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1509 : work1509.theta.ok = true ∧
    work1509.jac.invOK = true ∧ acceptsUnitSq work1509.out = true := by decide +kernel

def cell1509 : CellCertificate where
  tauBall := tau1509
  contactCenter := center1509
  contactBall := contact1509
  work := work1509
  center_sq := center_sq1509
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1509.1
  jac_ok := checks1509.2.1
  accepted := checks1509.2.2

def tau1510 : RatBall :=
  ⟨⟨-3/64, -113/320⟩, 3/640⟩
def center1510 : GaussianRat :=
  ⟨-18633993/500000000, -15969023/62500000⟩
def contact1510 : RatBall := localContactBall tau1510 center1510
def work1510 : RoundedTauEval :=
  evalTau precision tau1510 contact1510 logTwoBall

theorem center_sq1510 : (center1510.re : ℝ)^2 +
    (center1510.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1510]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1510 : work1510.theta.ok = true ∧
    work1510.jac.invOK = true ∧ acceptsUnitSq work1510.out = true := by decide +kernel

def cell1510 : CellCertificate where
  tauBall := tau1510
  contactCenter := center1510
  contactBall := contact1510
  work := work1510
  center_sq := center_sq1510
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1510.1
  jac_ok := checks1510.2.1
  accepted := checks1510.2.2

def tau1511 : RatBall :=
  ⟨⟨-13/320, -113/320⟩, 3/640⟩
def center1511 : GaussianRat :=
  ⟨-32309979/1000000000, -127843073/500000000⟩
def contact1511 : RatBall := localContactBall tau1511 center1511
def work1511 : RoundedTauEval :=
  evalTau precision tau1511 contact1511 logTwoBall

theorem center_sq1511 : (center1511.re : ℝ)^2 +
    (center1511.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1511]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1511 : work1511.theta.ok = true ∧
    work1511.jac.invOK = true ∧ acceptsUnitSq work1511.out = true := by decide +kernel

def cell1511 : CellCertificate where
  tauBall := tau1511
  contactCenter := center1511
  contactBall := contact1511
  work := work1511
  center_sq := center_sq1511
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1511.1
  jac_ok := checks1511.2.1
  accepted := checks1511.2.2

def cells : List CellCertificate := [cell1504, cell1505, cell1506, cell1507, cell1508, cell1509, cell1510, cell1511]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188


