-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0045_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0045_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:48:44.327493+00:00
-- url     : https://prove2.me/theorems/fc0825e1-06da-4250-af8e-1f8cd19f9560
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0045 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0360 : RatBall :=
  ⟨⟨-7/32, -41/160⟩, 3/320⟩
def center0360 : GaussianRat :=
  ⟨-31833667/200000000, -43062577/250000000⟩
def contact0360 : RatBall := localContactBall tau0360 center0360
def work0360 : RoundedTauEval :=
  evalTau precision tau0360 contact0360 logTwoBall

theorem center_sq0360 : (center0360.re : ℝ)^2 +
    (center0360.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0360]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0360 : work0360.theta.ok = true ∧
    work0360.jac.invOK = true ∧ acceptsUnitSq work0360.out = true := by decide +kernel

def cell0360 : CellCertificate where
  tauBall := tau0360
  contactCenter := center0360
  contactBall := contact0360
  work := work0360
  center_sq := center_sq0360
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0360.1
  jac_ok := checks0360.2.1
  accepted := checks0360.2.2

def tau0361 : RatBall :=
  ⟨⟨-33/160, -41/160⟩, 3/320⟩
def center0361 : GaussianRat :=
  ⟨-150430267/1000000000, -1082879/6250000⟩
def contact0361 : RatBall := localContactBall tau0361 center0361
def work0361 : RoundedTauEval :=
  evalTau precision tau0361 contact0361 logTwoBall

theorem center_sq0361 : (center0361.re : ℝ)^2 +
    (center0361.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0361]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0361 : work0361.theta.ok = true ∧
    work0361.jac.invOK = true ∧ acceptsUnitSq work0361.out = true := by decide +kernel

def cell0361 : CellCertificate where
  tauBall := tau0361
  contactCenter := center0361
  contactBall := contact0361
  work := work0361
  center_sq := center_sq0361
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0361.1
  jac_ok := checks0361.2.1
  accepted := checks0361.2.2

def tau0362 : RatBall :=
  ⟨⟨-9/32, -39/160⟩, 3/320⟩
def center0362 : GaussianRat :=
  ⟨-200670971/1000000000, -79101837/500000000⟩
def contact0362 : RatBall := localContactBall tau0362 center0362
def work0362 : RoundedTauEval :=
  evalTau precision tau0362 contact0362 logTwoBall

theorem center_sq0362 : (center0362.re : ℝ)^2 +
    (center0362.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0362]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0362 : work0362.theta.ok = true ∧
    work0362.jac.invOK = true ∧ acceptsUnitSq work0362.out = true := by decide +kernel

def cell0362 : CellCertificate where
  tauBall := tau0362
  contactCenter := center0362
  contactBall := contact0362
  work := work0362
  center_sq := center_sq0362
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0362.1
  jac_ok := checks0362.2.1
  accepted := checks0362.2.2

def tau0363 : RatBall :=
  ⟨⟨-47/160, -37/160⟩, 3/320⟩
def center0363 : GaussianRat :=
  ⟨-103902067/500000000, -37194907/250000000⟩
def contact0363 : RatBall := localContactBall tau0363 center0363
def work0363 : RoundedTauEval :=
  evalTau precision tau0363 contact0363 logTwoBall

theorem center_sq0363 : (center0363.re : ℝ)^2 +
    (center0363.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0363]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0363 : work0363.theta.ok = true ∧
    work0363.jac.invOK = true ∧ acceptsUnitSq work0363.out = true := by decide +kernel

def cell0363 : CellCertificate where
  tauBall := tau0363
  contactCenter := center0363
  contactBall := contact0363
  work := work0363
  center_sq := center_sq0363
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0363.1
  jac_ok := checks0363.2.1
  accepted := checks0363.2.2

def tau0364 : RatBall :=
  ⟨⟨-9/32, -37/160⟩, 3/320⟩
def center0364 : GaussianRat :=
  ⟨-199541503/1000000000, -74944839/500000000⟩
def contact0364 : RatBall := localContactBall tau0364 center0364
def work0364 : RoundedTauEval :=
  evalTau precision tau0364 contact0364 logTwoBall

theorem center_sq0364 : (center0364.re : ℝ)^2 +
    (center0364.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0364]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0364 : work0364.theta.ok = true ∧
    work0364.jac.invOK = true ∧ acceptsUnitSq work0364.out = true := by decide +kernel

def cell0364 : CellCertificate where
  tauBall := tau0364
  contactCenter := center0364
  contactBall := contact0364
  work := work0364
  center_sq := center_sq0364
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0364.1
  jac_ok := checks0364.2.1
  accepted := checks0364.2.2

def tau0365 : RatBall :=
  ⟨⟨-43/160, -39/160⟩, 3/320⟩
def center0365 : GaussianRat :=
  ⟨-96152483/500000000, -159351351/1000000000⟩
def contact0365 : RatBall := localContactBall tau0365 center0365
def work0365 : RoundedTauEval :=
  evalTau precision tau0365 contact0365 logTwoBall

theorem center_sq0365 : (center0365.re : ℝ)^2 +
    (center0365.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0365]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0365 : work0365.theta.ok = true ∧
    work0365.jac.invOK = true ∧ acceptsUnitSq work0365.out = true := by decide +kernel

def cell0365 : CellCertificate where
  tauBall := tau0365
  contactCenter := center0365
  contactBall := contact0365
  work := work0365
  center_sq := center_sq0365
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0365.1
  jac_ok := checks0365.2.1
  accepted := checks0365.2.2

def tau0366 : RatBall :=
  ⟨⟨-41/160, -39/160⟩, 3/320⟩
def center0366 : GaussianRat :=
  ⟨-91934683/500000000, -80231659/500000000⟩
def contact0366 : RatBall := localContactBall tau0366 center0366
def work0366 : RoundedTauEval :=
  evalTau precision tau0366 contact0366 logTwoBall

theorem center_sq0366 : (center0366.re : ℝ)^2 +
    (center0366.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0366]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045


