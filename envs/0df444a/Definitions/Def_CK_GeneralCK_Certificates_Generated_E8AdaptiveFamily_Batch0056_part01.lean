-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0056_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0056_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:16:04.146153+00:00
-- url     : https://prove2.me/theorems/7bb97cee-efc5-4af6-bc84-95642ed4c93c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0056 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0056_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0452 : RatBall :=
  ⟨⟨-21/160, -9/32⟩, 3/320⟩
def center0452 : GaussianRat :=
  ⟨-2456559/25000000, -19652513/100000000⟩
def contact0452 : RatBall := localContactBall tau0452 center0452
def work0452 : RoundedTauEval :=
  evalTau precision tau0452 contact0452 logTwoBall

theorem center_sq0452 : (center0452.re : ℝ)^2 +
    (center0452.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0452]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0452 : work0452.theta.ok = true ∧
    work0452.jac.invOK = true ∧ acceptsUnitSq work0452.out = true := by decide +kernel

def cell0452 : CellCertificate where
  tauBall := tau0452
  contactCenter := center0452
  contactBall := contact0452
  work := work0452
  center_sq := center_sq0452
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0452.1
  jac_ok := checks0452.2.1
  accepted := checks0452.2.2

def tau0453 : RatBall :=
  ⟨⟨-19/160, -47/160⟩, 3/320⟩
def center0453 : GaussianRat :=
  ⟨-89749431/1000000000, -206520639/1000000000⟩
def contact0453 : RatBall := localContactBall tau0453 center0453
def work0453 : RoundedTauEval :=
  evalTau precision tau0453 contact0453 logTwoBall

theorem center_sq0453 : (center0453.re : ℝ)^2 +
    (center0453.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0453]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0453 : work0453.theta.ok = true ∧
    work0453.jac.invOK = true ∧ acceptsUnitSq work0453.out = true := by decide +kernel

def cell0453 : CellCertificate where
  tauBall := tau0453
  contactCenter := center0453
  contactBall := contact0453
  work := work0453
  center_sq := center_sq0453
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0453.1
  jac_ok := checks0453.2.1
  accepted := checks0453.2.2

def tau0454 : RatBall :=
  ⟨⟨-17/160, -47/160⟩, 3/320⟩
def center0454 : GaussianRat :=
  ⟨-20104647/250000000, -10360657/50000000⟩
def contact0454 : RatBall := localContactBall tau0454 center0454
def work0454 : RoundedTauEval :=
  evalTau precision tau0454 contact0454 logTwoBall

theorem center_sq0454 : (center0454.re : ℝ)^2 +
    (center0454.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0454]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0454 : work0454.theta.ok = true ∧
    work0454.jac.invOK = true ∧ acceptsUnitSq work0454.out = true := by decide +kernel

def cell0454 : CellCertificate where
  tauBall := tau0454
  contactCenter := center0454
  contactBall := contact0454
  work := work0454
  center_sq := center_sq0454
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0454.1
  jac_ok := checks0454.2.1
  accepted := checks0454.2.2

def tau0455 : RatBall :=
  ⟨⟨-19/160, -9/32⟩, 3/320⟩
def center0455 : GaussianRat :=
  ⟨-22260513/250000000, -49311287/250000000⟩
def contact0455 : RatBall := localContactBall tau0455 center0455
def work0455 : RoundedTauEval :=
  evalTau precision tau0455 contact0455 logTwoBall

theorem center_sq0455 : (center0455.re : ℝ)^2 +
    (center0455.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0455]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0455 : work0455.theta.ok = true ∧
    work0455.jac.invOK = true ∧ acceptsUnitSq work0455.out = true := by decide +kernel

def cell0455 : CellCertificate where
  tauBall := tau0455
  contactCenter := center0455
  contactBall := contact0455
  work := work0455
  center_sq := center_sq0455
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0455.1
  jac_ok := checks0455.2.1
  accepted := checks0455.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056


