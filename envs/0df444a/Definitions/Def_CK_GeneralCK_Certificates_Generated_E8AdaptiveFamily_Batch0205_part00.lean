-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0205_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0205_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:13:16.484607+00:00
-- url     : https://prove2.me/theorems/8e5f0006-61b1-4d31-bb81-18c2b15db1b4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0205 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1640 : RatBall :=
  ⟨⟨39/320, -113/320⟩, 3/640⟩
def center1640 : GaussianRat :=
  ⟨48071341/500000000, -251379737/1000000000⟩
def contact1640 : RatBall := localContactBall tau1640 center1640
def work1640 : RoundedTauEval :=
  evalTau precision tau1640 contact1640 logTwoBall

theorem center_sq1640 : (center1640.re : ℝ)^2 +
    (center1640.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1640]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1640 : work1640.theta.ok = true ∧
    work1640.jac.invOK = true ∧ acceptsUnitSq work1640.out = true := by decide +kernel

def cell1640 : CellCertificate where
  tauBall := tau1640
  contactCenter := center1640
  contactBall := contact1640
  work := work1640
  center_sq := center_sq1640
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1640.1
  jac_ok := checks1640.2.1
  accepted := checks1640.2.2

def tau1641 : RatBall :=
  ⟨⟨41/320, -23/64⟩, 3/640⟩
def center1641 : GaussianRat :=
  ⟨12686743/125000000, -255720023/1000000000⟩
def contact1641 : RatBall := localContactBall tau1641 center1641
def work1641 : RoundedTauEval :=
  evalTau precision tau1641 contact1641 logTwoBall

theorem center_sq1641 : (center1641.re : ℝ)^2 +
    (center1641.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1641]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1641 : work1641.theta.ok = true ∧
    work1641.jac.invOK = true ∧ acceptsUnitSq work1641.out = true := by decide +kernel

def cell1641 : CellCertificate where
  tauBall := tau1641
  contactCenter := center1641
  contactBall := contact1641
  work := work1641
  center_sq := center_sq1641
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1641.1
  jac_ok := checks1641.2.1
  accepted := checks1641.2.2

def tau1642 : RatBall :=
  ⟨⟨43/320, -23/64⟩, 3/640⟩
def center1642 : GaussianRat :=
  ⟨106336973/1000000000, -255184583/1000000000⟩
def contact1642 : RatBall := localContactBall tau1642 center1642
def work1642 : RoundedTauEval :=
  evalTau precision tau1642 contact1642 logTwoBall

theorem center_sq1642 : (center1642.re : ℝ)^2 +
    (center1642.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1642]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1642 : work1642.theta.ok = true ∧
    work1642.jac.invOK = true ∧ acceptsUnitSq work1642.out = true := by decide +kernel

def cell1642 : CellCertificate where
  tauBall := tau1642
  contactCenter := center1642
  contactBall := contact1642
  work := work1642
  center_sq := center_sq1642
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1642.1
  jac_ok := checks1642.2.1
  accepted := checks1642.2.2

def tau1643 : RatBall :=
  ⟨⟨41/320, -113/320⟩, 3/640⟩
def center1643 : GaussianRat :=
  ⟨100977067/1000000000, -250881183/1000000000⟩
def contact1643 : RatBall := localContactBall tau1643 center1643
def work1643 : RoundedTauEval :=
  evalTau precision tau1643 contact1643 logTwoBall

theorem center_sq1643 : (center1643.re : ℝ)^2 +
    (center1643.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1643]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1643 : work1643.theta.ok = true ∧
    work1643.jac.invOK = true ∧ acceptsUnitSq work1643.out = true := by decide +kernel

def cell1643 : CellCertificate where
  tauBall := tau1643
  contactCenter := center1643
  contactBall := contact1643
  work := work1643
  center_sq := center_sq1643
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1643.1
  jac_ok := checks1643.2.1
  accepted := checks1643.2.2

def tau1644 : RatBall :=
  ⟨⟨43/320, -113/320⟩, 3/640⟩
def center1644 : GaussianRat :=
  ⟨105797499/1000000000, -62590039/250000000⟩
def contact1644 : RatBall := localContactBall tau1644 center1644
def work1644 : RoundedTauEval :=
  evalTau precision tau1644 contact1644 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205


