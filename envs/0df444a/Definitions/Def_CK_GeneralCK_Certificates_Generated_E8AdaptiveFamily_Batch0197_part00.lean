-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0197_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0197_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:29:53.299835+00:00
-- url     : https://prove2.me/theorems/65da3f3c-e27d-4e47-885e-b58105c7c581
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0197 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1576 : RatBall :=
  ⟨⟨9/320, -113/320⟩, 3/640⟩
def center1576 : GaussianRat :=
  ⟨22380501/1000000000, -127986203/500000000⟩
def contact1576 : RatBall := localContactBall tau1576 center1576
def work1576 : RoundedTauEval :=
  evalTau precision tau1576 contact1576 logTwoBall

theorem center_sq1576 : (center1576.re : ℝ)^2 +
    (center1576.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1576]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1576 : work1576.theta.ok = true ∧
    work1576.jac.invOK = true ∧ acceptsUnitSq work1576.out = true := by decide +kernel

def cell1576 : CellCertificate where
  tauBall := tau1576
  contactCenter := center1576
  contactBall := contact1576
  work := work1576
  center_sq := center_sq1576
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1576.1
  jac_ok := checks1576.2.1
  accepted := checks1576.2.2

def tau1577 : RatBall :=
  ⟨⟨11/320, -113/320⟩, 3/640⟩
def center1577 : GaussianRat :=
  ⟨5469449/200000000, -51168439/200000000⟩
def contact1577 : RatBall := localContactBall tau1577 center1577
def work1577 : RoundedTauEval :=
  evalTau precision tau1577 contact1577 logTwoBall

theorem center_sq1577 : (center1577.re : ℝ)^2 +
    (center1577.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1577]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1577 : work1577.theta.ok = true ∧
    work1577.jac.invOK = true ∧ acceptsUnitSq work1577.out = true := by decide +kernel

def cell1577 : CellCertificate where
  tauBall := tau1577
  contactCenter := center1577
  contactBall := contact1577
  work := work1577
  center_sq := center_sq1577
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1577.1
  jac_ok := checks1577.2.1
  accepted := checks1577.2.2

def tau1578 : RatBall :=
  ⟨⟨13/320, -23/64⟩, 3/640⟩
def center1578 : GaussianRat :=
  ⟨32481297/1000000000, -260659621/1000000000⟩
def contact1578 : RatBall := localContactBall tau1578 center1578
def work1578 : RoundedTauEval :=
  evalTau precision tau1578 contact1578 logTwoBall

theorem center_sq1578 : (center1578.re : ℝ)^2 +
    (center1578.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1578]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1578 : work1578.theta.ok = true ∧
    work1578.jac.invOK = true ∧ acceptsUnitSq work1578.out = true := by decide +kernel

def cell1578 : CellCertificate where
  tauBall := tau1578
  contactCenter := center1578
  contactBall := contact1578
  work := work1578
  center_sq := center_sq1578
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1578.1
  jac_ok := checks1578.2.1
  accepted := checks1578.2.2

def tau1579 : RatBall :=
  ⟨⟨3/64, -23/64⟩, 3/640⟩
def center1579 : GaussianRat :=
  ⟨37465331/1000000000, -260472693/1000000000⟩
def contact1579 : RatBall := localContactBall tau1579 center1579
def work1579 : RoundedTauEval :=
  evalTau precision tau1579 contact1579 logTwoBall

theorem center_sq1579 : (center1579.re : ℝ)^2 +
    (center1579.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1579]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1579 : work1579.theta.ok = true ∧
    work1579.jac.invOK = true ∧ acceptsUnitSq work1579.out = true := by decide +kernel

def cell1579 : CellCertificate where
  tauBall := tau1579
  contactCenter := center1579
  contactBall := contact1579
  work := work1579
  center_sq := center_sq1579
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1579.1
  jac_ok := checks1579.2.1
  accepted := checks1579.2.2

def tau1580 : RatBall :=
  ⟨⟨13/320, -113/320⟩, 3/640⟩
def center1580 : GaussianRat :=
  ⟨32309979/1000000000, -127843073/500000000⟩
def contact1580 : RatBall := localContactBall tau1580 center1580
def work1580 : RoundedTauEval :=
  evalTau precision tau1580 contact1580 logTwoBall

theorem center_sq1580 : (center1580.re : ℝ)^2 +
    (center1580.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1580]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1580 : work1580.theta.ok = true ∧
    work1580.jac.invOK = true ∧ acceptsUnitSq work1580.out = true := by decide +kernel

def cell1580 : CellCertificate where
  tauBall := tau1580
  contactCenter := center1580
  contactBall := contact1580
  work := work1580
  center_sq := center_sq1580
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1580.1
  jac_ok := checks1580.2.1
  accepted := checks1580.2.2

def tau1581 : RatBall :=
  ⟨⟨3/64, -113/320⟩, 3/640⟩
def center1581 : GaussianRat :=
  ⟨18633993/500000000, -15969023/62500000⟩
def contact1581 : RatBall := localContactBall tau1581 center1581
def work1581 : RoundedTauEval :=
  evalTau precision tau1581 contact1581 logTwoBall

theorem center_sq1581 : (center1581.re : ℝ)^2 +
    (center1581.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1581]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1581 : work1581.theta.ok = true ∧
    work1581.jac.invOK = true ∧ acceptsUnitSq work1581.out = true := by decide +kernel

def cell1581 : CellCertificate where
  tauBall := tau1581
  contactCenter := center1581
  contactBall := contact1581
  work := work1581
  center_sq := center_sq1581
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1581.1
  jac_ok := checks1581.2.1
  accepted := checks1581.2.2

def tau1582 : RatBall :=
  ⟨⟨17/320, -121/320⟩, 3/640⟩
def center1582 : GaussianRat :=
  ⟨8630399/200000000, -275306779/1000000000⟩
def contact1582 : RatBall := localContactBall tau1582 center1582
def work1582 : RoundedTauEval :=
  evalTau precision tau1582 contact1582 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197


