-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0165_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0165_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:13:11.592485+00:00
-- url     : https://prove2.me/theorems/dcf55244-28e7-4f49-a66e-ba446a27fefb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0165 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1320 : RatBall :=
  ⟨⟨-15/64, -19/64⟩, 3/640⟩
def center1320 : GaussianRat :=
  ⟨-43475599/250000000, -199203157/1000000000⟩
def contact1320 : RatBall := localContactBall tau1320 center1320
def work1320 : RoundedTauEval :=
  evalTau precision tau1320 contact1320 logTwoBall

theorem center_sq1320 : (center1320.re : ℝ)^2 +
    (center1320.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1320]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1320 : work1320.theta.ok = true ∧
    work1320.jac.invOK = true ∧ acceptsUnitSq work1320.out = true := by decide +kernel

def cell1320 : CellCertificate where
  tauBall := tau1320
  contactCenter := center1320
  contactBall := contact1320
  work := work1320
  center_sq := center_sq1320
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1320.1
  jac_ok := checks1320.2.1
  accepted := checks1320.2.2

def tau1321 : RatBall :=
  ⟨⟨-73/320, -19/64⟩, 3/640⟩
def center1321 : GaussianRat :=
  ⟨-16950309/100000000, -199854009/1000000000⟩
def contact1321 : RatBall := localContactBall tau1321 center1321
def work1321 : RoundedTauEval :=
  evalTau precision tau1321 contact1321 logTwoBall

theorem center_sq1321 : (center1321.re : ℝ)^2 +
    (center1321.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1321]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1321 : work1321.theta.ok = true ∧
    work1321.jac.invOK = true ∧ acceptsUnitSq work1321.out = true := by decide +kernel

def cell1321 : CellCertificate where
  tauBall := tau1321
  contactCenter := center1321
  contactBall := contact1321
  work := work1321
  center_sq := center_sq1321
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1321.1
  jac_ok := checks1321.2.1
  accepted := checks1321.2.2

def tau1322 : RatBall :=
  ⟨⟨-15/64, -93/320⟩, 3/640⟩
def center1322 : GaussianRat :=
  ⟨-173254189/1000000000, -38963859/200000000⟩
def contact1322 : RatBall := localContactBall tau1322 center1322
def work1322 : RoundedTauEval :=
  evalTau precision tau1322 contact1322 logTwoBall

theorem center_sq1322 : (center1322.re : ℝ)^2 +
    (center1322.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1322]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1322 : work1322.theta.ok = true ∧
    work1322.jac.invOK = true ∧ acceptsUnitSq work1322.out = true := by decide +kernel

def cell1322 : CellCertificate where
  tauBall := tau1322
  contactCenter := center1322
  contactBall := contact1322
  work := work1322
  center_sq := center_sq1322
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1322.1
  jac_ok := checks1322.2.1
  accepted := checks1322.2.2

def tau1323 : RatBall :=
  ⟨⟨-73/320, -93/320⟩, 3/640⟩
def center1323 : GaussianRat :=
  ⟨-84433841/500000000, -195452163/1000000000⟩
def contact1323 : RatBall := localContactBall tau1323 center1323
def work1323 : RoundedTauEval :=
  evalTau precision tau1323 contact1323 logTwoBall

theorem center_sq1323 : (center1323.re : ℝ)^2 +
    (center1323.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1323]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1323 : work1323.theta.ok = true ∧
    work1323.jac.invOK = true ∧ acceptsUnitSq work1323.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165


