-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0087_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0087_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:14:43.11141+00:00
-- url     : https://prove2.me/theorems/179c8e82-4f1c-4f1b-9c6e-d160e7c963bc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0087 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0696 : RatBall :=
  ⟨⟨39/160, -31/160⟩, 3/320⟩
def center0696 : GaussianRat :=
  ⟨10728219/62500000, -127685733/1000000000⟩
def contact0696 : RatBall := localContactBall tau0696 center0696
def work0696 : RoundedTauEval :=
  evalTau precision tau0696 contact0696 logTwoBall

theorem center_sq0696 : (center0696.re : ℝ)^2 +
    (center0696.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0696]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0696 : work0696.theta.ok = true ∧
    work0696.jac.invOK = true ∧ acceptsUnitSq work0696.out = true := by decide +kernel

def cell0696 : CellCertificate where
  tauBall := tau0696
  contactCenter := center0696
  contactBall := contact0696
  work := work0696
  center_sq := center_sq0696
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0696.1
  jac_ok := checks0696.2.1
  accepted := checks0696.2.2

def tau0697 : RatBall :=
  ⟨⟨37/160, -29/160⟩, 3/320⟩
def center0697 : GaussianRat :=
  ⟨81239917/500000000, -60019727/500000000⟩
def contact0697 : RatBall := localContactBall tau0697 center0697
def work0697 : RoundedTauEval :=
  evalTau precision tau0697 contact0697 logTwoBall

theorem center_sq0697 : (center0697.re : ℝ)^2 +
    (center0697.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0697]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0697 : work0697.theta.ok = true ∧
    work0697.jac.invOK = true ∧ acceptsUnitSq work0697.out = true := by decide +kernel

def cell0697 : CellCertificate where
  tauBall := tau0697
  contactCenter := center0697
  contactBall := contact0697
  work := work0697
  center_sq := center_sq0697
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0697.1
  jac_ok := checks0697.2.1
  accepted := checks0697.2.2

def tau0698 : RatBall :=
  ⟨⟨39/160, -29/160⟩, 3/320⟩
def center0698 : GaussianRat :=
  ⟨2135923/12500000, -119305389/1000000000⟩
def contact0698 : RatBall := localContactBall tau0698 center0698
def work0698 : RoundedTauEval :=
  evalTau precision tau0698 contact0698 logTwoBall

theorem center_sq0698 : (center0698.re : ℝ)^2 +
    (center0698.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0698]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0698 : work0698.theta.ok = true ∧
    work0698.jac.invOK = true ∧ acceptsUnitSq work0698.out = true := by decide +kernel

def cell0698 : CellCertificate where
  tauBall := tau0698
  contactCenter := center0698
  contactBall := contact0698
  work := work0698
  center_sq := center_sq0698
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0698.1
  jac_ok := checks0698.2.1
  accepted := checks0698.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087


