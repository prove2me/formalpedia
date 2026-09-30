-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0108_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0108_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:07:02.696075+00:00
-- url     : https://prove2.me/theorems/018b4741-9f96-473f-9eef-64fc042ee0c0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0108 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0108_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0867 : RatBall :=
  ⟨⟨-41/160, 37/160⟩, 3/320⟩
def center0867 : GaussianRat :=
  ⟨-182809387/1000000000, 76006029/500000000⟩
def contact0867 : RatBall := localContactBall tau0867 center0867
def work0867 : RoundedTauEval :=
  evalTau precision tau0867 contact0867 logTwoBall

theorem center_sq0867 : (center0867.re : ℝ)^2 +
    (center0867.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0867]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0867 : work0867.theta.ok = true ∧
    work0867.jac.invOK = true ∧ acceptsUnitSq work0867.out = true := by decide +kernel

def cell0867 : CellCertificate where
  tauBall := tau0867
  contactCenter := center0867
  contactBall := contact0867
  work := work0867
  center_sq := center_sq0867
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0867.1
  jac_ok := checks0867.2.1
  accepted := checks0867.2.2

def tau0868 : RatBall :=
  ⟨⟨-43/160, 39/160⟩, 3/320⟩
def center0868 : GaussianRat :=
  ⟨-96152483/500000000, 159351351/1000000000⟩
def contact0868 : RatBall := localContactBall tau0868 center0868
def work0868 : RoundedTauEval :=
  evalTau precision tau0868 contact0868 logTwoBall

theorem center_sq0868 : (center0868.re : ℝ)^2 +
    (center0868.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0868]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0868 : work0868.theta.ok = true ∧
    work0868.jac.invOK = true ∧ acceptsUnitSq work0868.out = true := by decide +kernel

def cell0868 : CellCertificate where
  tauBall := tau0868
  contactCenter := center0868
  contactBall := contact0868
  work := work0868
  center_sq := center_sq0868
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0868.1
  jac_ok := checks0868.2.1
  accepted := checks0868.2.2

def tau0869 : RatBall :=
  ⟨⟨-41/160, 39/160⟩, 3/320⟩
def center0869 : GaussianRat :=
  ⟨-91934683/500000000, 80231659/500000000⟩
def contact0869 : RatBall := localContactBall tau0869 center0869
def work0869 : RoundedTauEval :=
  evalTau precision tau0869 contact0869 logTwoBall

theorem center_sq0869 : (center0869.re : ℝ)^2 +
    (center0869.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0869]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0869 : work0869.theta.ok = true ∧
    work0869.jac.invOK = true ∧ acceptsUnitSq work0869.out = true := by decide +kernel

def cell0869 : CellCertificate where
  tauBall := tau0869
  contactCenter := center0869
  contactBall := contact0869
  work := work0869
  center_sq := center_sq0869
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0869.1
  jac_ok := checks0869.2.1
  accepted := checks0869.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108


