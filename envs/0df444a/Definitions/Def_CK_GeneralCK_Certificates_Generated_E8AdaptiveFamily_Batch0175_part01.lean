-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0175_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0175_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:11:57.51052+00:00
-- url     : https://prove2.me/theorems/275b373d-dd22-4377-97b3-465f340d9d98
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0175 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0175_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1404 : RatBall :=
  ⟨⟨-63/320, -99/320⟩, 3/640⟩
def center1404 : GaussianRat :=
  ⟨-148426041/1000000000, -105961569/500000000⟩
def contact1404 : RatBall := localContactBall tau1404 center1404
def work1404 : RoundedTauEval :=
  evalTau precision tau1404 contact1404 logTwoBall

theorem center_sq1404 : (center1404.re : ℝ)^2 +
    (center1404.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1404]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1404 : work1404.theta.ok = true ∧
    work1404.jac.invOK = true ∧ acceptsUnitSq work1404.out = true := by decide +kernel

def cell1404 : CellCertificate where
  tauBall := tau1404
  contactCenter := center1404
  contactBall := contact1404
  work := work1404
  center_sq := center_sq1404
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1404.1
  jac_ok := checks1404.2.1
  accepted := checks1404.2.2

def tau1405 : RatBall :=
  ⟨⟨-61/320, -99/320⟩, 3/640⟩
def center1405 : GaussianRat :=
  ⟨-28778703/200000000, -106261649/500000000⟩
def contact1405 : RatBall := localContactBall tau1405 center1405
def work1405 : RoundedTauEval :=
  evalTau precision tau1405 contact1405 logTwoBall

theorem center_sq1405 : (center1405.re : ℝ)^2 +
    (center1405.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1405]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1405 : work1405.theta.ok = true ∧
    work1405.jac.invOK = true ∧ acceptsUnitSq work1405.out = true := by decide +kernel

def cell1405 : CellCertificate where
  tauBall := tau1405
  contactCenter := center1405
  contactBall := contact1405
  work := work1405
  center_sq := center_sq1405
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1405.1
  jac_ok := checks1405.2.1
  accepted := checks1405.2.2

def tau1406 : RatBall :=
  ⟨⟨-63/320, -97/320⟩, 3/640⟩
def center1406 : GaussianRat :=
  ⟨-147826489/1000000000, -2592583/12500000⟩
def contact1406 : RatBall := localContactBall tau1406 center1406
def work1406 : RoundedTauEval :=
  evalTau precision tau1406 contact1406 logTwoBall

theorem center_sq1406 : (center1406.re : ℝ)^2 +
    (center1406.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1406]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1406 : work1406.theta.ok = true ∧
    work1406.jac.invOK = true ∧ acceptsUnitSq work1406.out = true := by decide +kernel

def cell1406 : CellCertificate where
  tauBall := tau1406
  contactCenter := center1406
  contactBall := contact1406
  work := work1406
  center_sq := center_sq1406
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1406.1
  jac_ok := checks1406.2.1
  accepted := checks1406.2.2

def tau1407 : RatBall :=
  ⟨⟨-61/320, -97/320⟩, 3/640⟩
def center1407 : GaussianRat :=
  ⟨-143309371/1000000000, -103995141/500000000⟩
def contact1407 : RatBall := localContactBall tau1407 center1407
def work1407 : RoundedTauEval :=
  evalTau precision tau1407 contact1407 logTwoBall

theorem center_sq1407 : (center1407.re : ℝ)^2 +
    (center1407.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1407]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1407 : work1407.theta.ok = true ∧
    work1407.jac.invOK = true ∧ acceptsUnitSq work1407.out = true := by decide +kernel

def cell1407 : CellCertificate where
  tauBall := tau1407
  contactCenter := center1407
  contactBall := contact1407
  work := work1407
  center_sq := center_sq1407
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1407.1
  jac_ok := checks1407.2.1
  accepted := checks1407.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175


