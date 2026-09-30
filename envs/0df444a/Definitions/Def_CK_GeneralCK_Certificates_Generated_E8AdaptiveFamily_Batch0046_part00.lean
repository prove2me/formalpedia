-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0046_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0046_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:06:37.895+00:00
-- url     : https://prove2.me/theorems/94eb0ba3-84f3-4ea6-b1cc-7accfa3d8095
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0046 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0368 : RatBall :=
  ⟨⟨-41/160, -37/160⟩, 3/320⟩
def center0368 : GaussianRat :=
  ⟨-182809387/1000000000, -76006029/500000000⟩
def contact0368 : RatBall := localContactBall tau0368 center0368
def work0368 : RoundedTauEval :=
  evalTau precision tau0368 contact0368 logTwoBall

theorem center_sq0368 : (center0368.re : ℝ)^2 +
    (center0368.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0368]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0368 : work0368.theta.ok = true ∧
    work0368.jac.invOK = true ∧ acceptsUnitSq work0368.out = true := by decide +kernel

def cell0368 : CellCertificate where
  tauBall := tau0368
  contactCenter := center0368
  contactBall := contact0368
  work := work0368
  center_sq := center_sq0368
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0368.1
  jac_ok := checks0368.2.1
  accepted := checks0368.2.2

def tau0369 : RatBall :=
  ⟨⟨-47/160, -7/32⟩, 3/320⟩
def center0369 : GaussianRat :=
  ⟨-206714057/1000000000, -70283583/500000000⟩
def contact0369 : RatBall := localContactBall tau0369 center0369
def work0369 : RoundedTauEval :=
  evalTau precision tau0369 contact0369 logTwoBall

theorem center_sq0369 : (center0369.re : ℝ)^2 +
    (center0369.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0369]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0369 : work0369.theta.ok = true ∧
    work0369.jac.invOK = true ∧ acceptsUnitSq work0369.out = true := by decide +kernel

def cell0369 : CellCertificate where
  tauBall := tau0369
  contactCenter := center0369
  contactBall := contact0369
  work := work0369
  center_sq := center_sq0369
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0369.1
  jac_ok := checks0369.2.1
  accepted := checks0369.2.2

def tau0370 : RatBall :=
  ⟨⟨-9/32, -7/32⟩, 3/320⟩
def center0370 : GaussianRat :=
  ⟨-49620407/250000000, -141607653/1000000000⟩
def contact0370 : RatBall := localContactBall tau0370 center0370
def work0370 : RoundedTauEval :=
  evalTau precision tau0370 contact0370 logTwoBall

theorem center_sq0370 : (center0370.re : ℝ)^2 +
    (center0370.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0370]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0370 : work0370.theta.ok = true ∧
    work0370.jac.invOK = true ∧ acceptsUnitSq work0370.out = true := by decide +kernel

def cell0370 : CellCertificate where
  tauBall := tau0370
  contactCenter := center0370
  contactBall := contact0370
  work := work0370
  center_sq := center_sq0370
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0370.1
  jac_ok := checks0370.2.1
  accepted := checks0370.2.2

def tau0371 : RatBall :=
  ⟨⟨-47/160, -33/160⟩, 3/320⟩
def center0371 : GaussianRat :=
  ⟨-205693537/1000000000, -132383201/1000000000⟩
def contact0371 : RatBall := localContactBall tau0371 center0371
def work0371 : RoundedTauEval :=
  evalTau precision tau0371 contact0371 logTwoBall

theorem center_sq0371 : (center0371.re : ℝ)^2 +
    (center0371.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0371]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0371 : work0371.theta.ok = true ∧
    work0371.jac.invOK = true ∧ acceptsUnitSq work0371.out = true := by decide +kernel

def cell0371 : CellCertificate where
  tauBall := tau0371
  contactCenter := center0371
  contactBall := contact0371
  work := work0371
  center_sq := center_sq0371
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0371.1
  jac_ok := checks0371.2.1
  accepted := checks0371.2.2

def tau0372 : RatBall :=
  ⟨⟨-9/32, -33/160⟩, 3/320⟩
def center0372 : GaussianRat :=
  ⟨-197489591/1000000000, -66677907/500000000⟩
def contact0372 : RatBall := localContactBall tau0372 center0372
def work0372 : RoundedTauEval :=
  evalTau precision tau0372 contact0372 logTwoBall

theorem center_sq0372 : (center0372.re : ℝ)^2 +
    (center0372.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0372]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0372 : work0372.theta.ok = true ∧
    work0372.jac.invOK = true ∧ acceptsUnitSq work0372.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046


