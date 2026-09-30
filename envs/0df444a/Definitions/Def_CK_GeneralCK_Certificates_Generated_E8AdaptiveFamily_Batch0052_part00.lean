-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0052_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0052_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:32:45.871638+00:00
-- url     : https://prove2.me/theorems/6d823e9e-5008-4c91-8925-7a190636536e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0052 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0416 : RatBall :=
  ⟨⟨-9/160, -49/160⟩, 3/320⟩
def center0416 : GaussianRat :=
  ⟨-43120523/1000000000, -109375967/500000000⟩
def contact0416 : RatBall := localContactBall tau0416 center0416
def work0416 : RoundedTauEval :=
  evalTau precision tau0416 contact0416 logTwoBall

theorem center_sq0416 : (center0416.re : ℝ)^2 +
    (center0416.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0416]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0416 : work0416.theta.ok = true ∧
    work0416.jac.invOK = true ∧ acceptsUnitSq work0416.out = true := by decide +kernel

def cell0416 : CellCertificate where
  tauBall := tau0416
  contactCenter := center0416
  contactBall := contact0416
  work := work0416
  center_sq := center_sq0416
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0416.1
  jac_ok := checks0416.2.1
  accepted := checks0416.2.2

def tau0417 : RatBall :=
  ⟨⟨-7/160, -11/32⟩, 3/320⟩
def center0417 : GaussianRat :=
  ⟨-6904519/200000000, -248189889/1000000000⟩
def contact0417 : RatBall := localContactBall tau0417 center0417
def work0417 : RoundedTauEval :=
  evalTau precision tau0417 contact0417 logTwoBall

theorem center_sq0417 : (center0417.re : ℝ)^2 +
    (center0417.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0417]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0417 : work0417.theta.ok = true ∧
    work0417.jac.invOK = true ∧ acceptsUnitSq work0417.out = true := by decide +kernel

def cell0417 : CellCertificate where
  tauBall := tau0417
  contactCenter := center0417
  contactBall := contact0417
  work := work0417
  center_sq := center_sq0417
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0417.1
  jac_ok := checks0417.2.1
  accepted := checks0417.2.2

def tau0418 : RatBall :=
  ⟨⟨-1/32, -11/32⟩, 3/320⟩
def center0418 : GaussianRat :=
  ⟨-24673061/1000000000, -248489097/1000000000⟩
def contact0418 : RatBall := localContactBall tau0418 center0418
def work0418 : RoundedTauEval :=
  evalTau precision tau0418 contact0418 logTwoBall

theorem center_sq0418 : (center0418.re : ℝ)^2 +
    (center0418.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0418]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0418 : work0418.theta.ok = true ∧
    work0418.jac.invOK = true ∧ acceptsUnitSq work0418.out = true := by decide +kernel

def cell0418 : CellCertificate where
  tauBall := tau0418
  contactCenter := center0418
  contactBall := contact0418
  work := work0418
  center_sq := center_sq0418
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0418.1
  jac_ok := checks0418.2.1
  accepted := checks0418.2.2

def tau0419 : RatBall :=
  ⟨⟨-7/160, -53/160⟩, 3/320⟩
def center0419 : GaussianRat :=
  ⟨-17091823/500000000, -119198781/500000000⟩
def contact0419 : RatBall := localContactBall tau0419 center0419
def work0419 : RoundedTauEval :=
  evalTau precision tau0419 contact0419 logTwoBall

theorem center_sq0419 : (center0419.re : ℝ)^2 +
    (center0419.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0419]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0419 : work0419.theta.ok = true ∧
    work0419.jac.invOK = true ∧ acceptsUnitSq work0419.out = true := by decide +kernel

def cell0419 : CellCertificate where
  tauBall := tau0419
  contactCenter := center0419
  contactBall := contact0419
  work := work0419
  center_sq := center_sq0419
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0419.1
  jac_ok := checks0419.2.1
  accepted := checks0419.2.2

def tau0420 : RatBall :=
  ⟨⟨-1/32, -53/160⟩, 3/320⟩
def center0420 : GaussianRat :=
  ⟨-2443029/100000000, -119340169/500000000⟩
def contact0420 : RatBall := localContactBall tau0420 center0420
def work0420 : RoundedTauEval :=
  evalTau precision tau0420 contact0420 logTwoBall

theorem center_sq0420 : (center0420.re : ℝ)^2 +
    (center0420.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0420]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0420 : work0420.theta.ok = true ∧
    work0420.jac.invOK = true ∧ acceptsUnitSq work0420.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052


