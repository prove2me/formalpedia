-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0053_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0053_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:11:39.401587+00:00
-- url     : https://prove2.me/theorems/763b8510-6845-4a76-879f-78b88e42b334
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0053 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0424 : RatBall :=
  ⟨⟨-1/160, -53/160⟩, 3/320⟩
def center0424 : GaussianRat :=
  ⟨-611093/125000000, -238963881/1000000000⟩
def contact0424 : RatBall := localContactBall tau0424 center0424
def work0424 : RoundedTauEval :=
  evalTau precision tau0424 contact0424 logTwoBall

theorem center_sq0424 : (center0424.re : ℝ)^2 +
    (center0424.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0424]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0424 : work0424.theta.ok = true ∧
    work0424.jac.invOK = true ∧ acceptsUnitSq work0424.out = true := by decide +kernel

def cell0424 : CellCertificate where
  tauBall := tau0424
  contactCenter := center0424
  contactBall := contact0424
  work := work0424
  center_sq := center_sq0424
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0424.1
  jac_ok := checks0424.2.1
  accepted := checks0424.2.2

def tau0425 : RatBall :=
  ⟨⟨-7/160, -51/160⟩, 3/320⟩
def center0425 : GaussianRat :=
  ⟨-1693169/50000000, -228698347/1000000000⟩
def contact0425 : RatBall := localContactBall tau0425 center0425
def work0425 : RoundedTauEval :=
  evalTau precision tau0425 contact0425 logTwoBall

theorem center_sq0425 : (center0425.re : ℝ)^2 +
    (center0425.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0425]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0425 : work0425.theta.ok = true ∧
    work0425.jac.invOK = true ∧ acceptsUnitSq work0425.out = true := by decide +kernel

def cell0425 : CellCertificate where
  tauBall := tau0425
  contactCenter := center0425
  contactBall := contact0425
  work := work0425
  center_sq := center_sq0425
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0425.1
  jac_ok := checks0425.2.1
  accepted := checks0425.2.2

def tau0426 : RatBall :=
  ⟨⟨-1/32, -51/160⟩, 3/320⟩
def center0426 : GaussianRat :=
  ⟨-24200917/1000000000, -228965453/1000000000⟩
def contact0426 : RatBall := localContactBall tau0426 center0426
def work0426 : RoundedTauEval :=
  evalTau precision tau0426 contact0426 logTwoBall

theorem center_sq0426 : (center0426.re : ℝ)^2 +
    (center0426.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0426]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0426 : work0426.theta.ok = true ∧
    work0426.jac.invOK = true ∧ acceptsUnitSq work0426.out = true := by decide +kernel

def cell0426 : CellCertificate where
  tauBall := tau0426
  contactCenter := center0426
  contactBall := contact0426
  work := work0426
  center_sq := center_sq0426
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0426.1
  jac_ok := checks0426.2.1
  accepted := checks0426.2.2

def tau0427 : RatBall :=
  ⟨⟨-7/160, -49/160⟩, 3/320⟩
def center0427 : GaussianRat :=
  ⟨-16780473/500000000, -219087113/1000000000⟩
def contact0427 : RatBall := localContactBall tau0427 center0427
def work0427 : RoundedTauEval :=
  evalTau precision tau0427 contact0427 logTwoBall

theorem center_sq0427 : (center0427.re : ℝ)^2 +
    (center0427.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0427]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0427 : work0427.theta.ok = true ∧
    work0427.jac.invOK = true ∧ acceptsUnitSq work0427.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053


