-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0043_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0043_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:28:30.809+00:00
-- url     : https://prove2.me/theorems/d0ab5f0a-5737-43b7-a4c8-3ca79a4e4c5f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0043 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0043_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell0347 : CellCertificate where
  tauBall := tau0347
  contactCenter := center0347
  contactBall := contact0347
  work := work0347
  center_sq := center_sq0347
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0347.1
  jac_ok := checks0347.2.1
  accepted := checks0347.2.2

def tau0348 : RatBall :=
  ⟨⟨-51/160, -33/160⟩, 3/320⟩
def center0348 : GaussianRat :=
  ⟨-13868507/62500000, -13035901/100000000⟩
def contact0348 : RatBall := localContactBall tau0348 center0348
def work0348 : RoundedTauEval :=
  evalTau precision tau0348 contact0348 logTwoBall

theorem center_sq0348 : (center0348.re : ℝ)^2 +
    (center0348.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0348]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0348 : work0348.theta.ok = true ∧
    work0348.jac.invOK = true ∧ acceptsUnitSq work0348.out = true := by decide +kernel

def cell0348 : CellCertificate where
  tauBall := tau0348
  contactCenter := center0348
  contactBall := contact0348
  work := work0348
  center_sq := center_sq0348
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0348.1
  jac_ok := checks0348.2.1
  accepted := checks0348.2.2

def tau0349 : RatBall :=
  ⟨⟨-49/160, -33/160⟩, 3/320⟩
def center0349 : GaussianRat :=
  ⟨-8553183/40000000, -26276749/200000000⟩
def contact0349 : RatBall := localContactBall tau0349 center0349
def work0349 : RoundedTauEval :=
  evalTau precision tau0349 contact0349 logTwoBall

theorem center_sq0349 : (center0349.re : ℝ)^2 +
    (center0349.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0349]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0349 : work0349.theta.ok = true ∧
    work0349.jac.invOK = true ∧ acceptsUnitSq work0349.out = true := by decide +kernel

def cell0349 : CellCertificate where
  tauBall := tau0349
  contactCenter := center0349
  contactBall := contact0349
  work := work0349
  center_sq := center_sq0349
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0349.1
  jac_ok := checks0349.2.1
  accepted := checks0349.2.2

def tau0350 : RatBall :=
  ⟨⟨-43/160, -41/160⟩, 3/320⟩
def center0350 : GaussianRat :=
  ⟨-193470247/1000000000, -167770653/1000000000⟩
def contact0350 : RatBall := localContactBall tau0350 center0350
def work0350 : RoundedTauEval :=
  evalTau precision tau0350 contact0350 logTwoBall

theorem center_sq0350 : (center0350.re : ℝ)^2 +
    (center0350.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0350]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0350 : work0350.theta.ok = true ∧
    work0350.jac.invOK = true ∧ acceptsUnitSq work0350.out = true := by decide +kernel

def cell0350 : CellCertificate where
  tauBall := tau0350
  contactCenter := center0350
  contactBall := contact0350
  work := work0350
  center_sq := center_sq0350
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0350.1
  jac_ok := checks0350.2.1
  accepted := checks0350.2.2

def tau0351 : RatBall :=
  ⟨⟨-41/160, -41/160⟩, 3/320⟩
def center0351 : GaussianRat :=
  ⟨-184996961/1000000000, -21119029/125000000⟩
def contact0351 : RatBall := localContactBall tau0351 center0351
def work0351 : RoundedTauEval :=
  evalTau precision tau0351 contact0351 logTwoBall

theorem center_sq0351 : (center0351.re : ℝ)^2 +
    (center0351.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0351]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043


