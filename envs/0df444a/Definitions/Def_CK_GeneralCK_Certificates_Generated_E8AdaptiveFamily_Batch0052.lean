-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0052
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0052
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:11:31.991424+00:00
-- url     : https://prove2.me/theorems/9ceae1b2-f4c8-470c-9f3c-1f90f37ecb1c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0052.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0052_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell0420 : CellCertificate where
  tauBall := tau0420
  contactCenter := center0420
  contactBall := contact0420
  work := work0420
  center_sq := center_sq0420
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0420.1
  jac_ok := checks0420.2.1
  accepted := checks0420.2.2

def tau0421 : RatBall :=
  ⟨⟨-3/160, -11/32⟩, 3/320⟩
def center0421 : GaussianRat :=
  ⟨-7404737/500000000, -31086129/125000000⟩
def contact0421 : RatBall := localContactBall tau0421 center0421
def work0421 : RoundedTauEval :=
  evalTau precision tau0421 contact0421 logTwoBall

theorem center_sq0421 : (center0421.re : ℝ)^2 +
    (center0421.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0421]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0421 : work0421.theta.ok = true ∧
    work0421.jac.invOK = true ∧ acceptsUnitSq work0421.out = true := by decide +kernel

def cell0421 : CellCertificate where
  tauBall := tau0421
  contactCenter := center0421
  contactBall := contact0421
  work := work0421
  center_sq := center_sq0421
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0421.1
  jac_ok := checks0421.2.1
  accepted := checks0421.2.2

def tau0422 : RatBall :=
  ⟨⟨-1/160, -11/32⟩, 3/320⟩
def center0422 : GaussianRat :=
  ⟨-617179/125000000, -248789139/1000000000⟩
def contact0422 : RatBall := localContactBall tau0422 center0422
def work0422 : RoundedTauEval :=
  evalTau precision tau0422 contact0422 logTwoBall

theorem center_sq0422 : (center0422.re : ℝ)^2 +
    (center0422.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0422]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0422 : work0422.theta.ok = true ∧
    work0422.jac.invOK = true ∧ acceptsUnitSq work0422.out = true := by decide +kernel

def cell0422 : CellCertificate where
  tauBall := tau0422
  contactCenter := center0422
  contactBall := contact0422
  work := work0422
  center_sq := center_sq0422
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0422.1
  jac_ok := checks0422.2.1
  accepted := checks0422.2.2

def tau0423 : RatBall :=
  ⟨⟨-3/160, -53/160⟩, 3/320⟩
def center0423 : GaussianRat :=
  ⟨-1832943/125000000, -238869281/1000000000⟩
def contact0423 : RatBall := localContactBall tau0423 center0423
def work0423 : RoundedTauEval :=
  evalTau precision tau0423 contact0423 logTwoBall

theorem center_sq0423 : (center0423.re : ℝ)^2 +
    (center0423.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0423]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0423 : work0423.theta.ok = true ∧
    work0423.jac.invOK = true ∧ acceptsUnitSq work0423.out = true := by decide +kernel

def cell0423 : CellCertificate where
  tauBall := tau0423
  contactCenter := center0423
  contactBall := contact0423
  work := work0423
  center_sq := center_sq0423
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0423.1
  jac_ok := checks0423.2.1
  accepted := checks0423.2.2

def cells : List CellCertificate := [cell0416, cell0417, cell0418, cell0419, cell0420, cell0421, cell0422, cell0423]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052


