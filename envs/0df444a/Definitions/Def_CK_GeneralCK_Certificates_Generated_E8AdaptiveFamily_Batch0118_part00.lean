-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0118_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0118_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:15:43.528591+00:00
-- url     : https://prove2.me/theorems/a7b54be7-11d7-4f78-9425-8bd9d48d6c37
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0118 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0944 : RatBall :=
  ⟨⟨-11/160, 47/160⟩, 3/320⟩
def center0944 : GaussianRat :=
  ⟨-13053307/250000000, 208849073/1000000000⟩
def contact0944 : RatBall := localContactBall tau0944 center0944
def work0944 : RoundedTauEval :=
  evalTau precision tau0944 contact0944 logTwoBall

theorem center_sq0944 : (center0944.re : ℝ)^2 +
    (center0944.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0944]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0944 : work0944.theta.ok = true ∧
    work0944.jac.invOK = true ∧ acceptsUnitSq work0944.out = true := by decide +kernel

def cell0944 : CellCertificate where
  tauBall := tau0944
  contactCenter := center0944
  contactBall := contact0944
  work := work0944
  center_sq := center_sq0944
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0944.1
  jac_ok := checks0944.2.1
  accepted := checks0944.2.2

def tau0945 : RatBall :=
  ⟨⟨-9/160, 47/160⟩, 3/320⟩
def center0945 : GaussianRat :=
  ⟨-42754839/1000000000, 41848559/200000000⟩
def contact0945 : RatBall := localContactBall tau0945 center0945
def work0945 : RoundedTauEval :=
  evalTau precision tau0945 contact0945 logTwoBall

theorem center_sq0945 : (center0945.re : ℝ)^2 +
    (center0945.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0945]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0945 : work0945.theta.ok = true ∧
    work0945.jac.invOK = true ∧ acceptsUnitSq work0945.out = true := by decide +kernel

def cell0945 : CellCertificate where
  tauBall := tau0945
  contactCenter := center0945
  contactBall := contact0945
  work := work0945
  center_sq := center_sq0945
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0945.1
  jac_ok := checks0945.2.1
  accepted := checks0945.2.2

def tau0946 : RatBall :=
  ⟨⟨-27/160, 49/160⟩, 3/320⟩
def center0946 : GaussianRat :=
  ⟨-3988651/31250000, 53050431/250000000⟩
def contact0946 : RatBall := localContactBall tau0946 center0946
def work0946 : RoundedTauEval :=
  evalTau precision tau0946 contact0946 logTwoBall

theorem center_sq0946 : (center0946.re : ℝ)^2 +
    (center0946.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0946]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0946 : work0946.theta.ok = true ∧
    work0946.jac.invOK = true ∧ acceptsUnitSq work0946.out = true := by decide +kernel

def cell0946 : CellCertificate where
  tauBall := tau0946
  contactCenter := center0946
  contactBall := contact0946
  work := work0946
  center_sq := center_sq0946
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0946.1
  jac_ok := checks0946.2.1
  accepted := checks0946.2.2

def tau0947 : RatBall :=
  ⟨⟨-5/32, 49/160⟩, 3/320⟩
def center0947 : GaussianRat :=
  ⟨-23686489/200000000, 53305887/250000000⟩
def contact0947 : RatBall := localContactBall tau0947 center0947
def work0947 : RoundedTauEval :=
  evalTau precision tau0947 contact0947 logTwoBall

theorem center_sq0947 : (center0947.re : ℝ)^2 +
    (center0947.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0947]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0947 : work0947.theta.ok = true ∧
    work0947.jac.invOK = true ∧ acceptsUnitSq work0947.out = true := by decide +kernel

def cell0947 : CellCertificate where
  tauBall := tau0947
  contactCenter := center0947
  contactBall := contact0947
  work := work0947
  center_sq := center_sq0947
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0947.1
  jac_ok := checks0947.2.1
  accepted := checks0947.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118


