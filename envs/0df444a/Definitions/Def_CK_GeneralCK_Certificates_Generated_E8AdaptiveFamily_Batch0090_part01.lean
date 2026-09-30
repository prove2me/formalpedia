-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0090_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0090_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:23:21.07679+00:00
-- url     : https://prove2.me/theorems/4f2c3119-7069-4a2a-90f0-4335784b8a00
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0090 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0090_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0724 : RatBall :=
  ⟨⟨11/32, -27/160⟩, 3/320⟩
def center0724 : GaussianRat :=
  ⟨234895911/1000000000, -52333711/500000000⟩
def contact0724 : RatBall := localContactBall tau0724 center0724
def work0724 : RoundedTauEval :=
  evalTau precision tau0724 contact0724 logTwoBall

theorem center_sq0724 : (center0724.re : ℝ)^2 +
    (center0724.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0724]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0724 : work0724.theta.ok = true ∧
    work0724.jac.invOK = true ∧ acceptsUnitSq work0724.out = true := by decide +kernel

def cell0724 : CellCertificate where
  tauBall := tau0724
  contactCenter := center0724
  contactBall := contact0724
  work := work0724
  center_sq := center_sq0724
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0724.1
  jac_ok := checks0724.2.1
  accepted := checks0724.2.2

def tau0725 : RatBall :=
  ⟨⟨53/160, -5/32⟩, 3/320⟩
def center0725 : GaussianRat :=
  ⟨226215887/1000000000, -24408867/250000000⟩
def contact0725 : RatBall := localContactBall tau0725 center0725
def work0725 : RoundedTauEval :=
  evalTau precision tau0725 contact0725 logTwoBall

theorem center_sq0725 : (center0725.re : ℝ)^2 +
    (center0725.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0725]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0725 : work0725.theta.ok = true ∧
    work0725.jac.invOK = true ∧ acceptsUnitSq work0725.out = true := by decide +kernel

def cell0725 : CellCertificate where
  tauBall := tau0725
  contactCenter := center0725
  contactBall := contact0725
  work := work0725
  center_sq := center_sq0725
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0725.1
  jac_ok := checks0725.2.1
  accepted := checks0725.2.2

def tau0726 : RatBall :=
  ⟨⟨11/32, -5/32⟩, 3/320⟩
def center0726 : GaussianRat :=
  ⟨234063587/1000000000, -96845571/1000000000⟩
def contact0726 : RatBall := localContactBall tau0726 center0726
def work0726 : RoundedTauEval :=
  evalTau precision tau0726 contact0726 logTwoBall

theorem center_sq0726 : (center0726.re : ℝ)^2 +
    (center0726.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0726]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0726 : work0726.theta.ok = true ∧
    work0726.jac.invOK = true ∧ acceptsUnitSq work0726.out = true := by decide +kernel

def cell0726 : CellCertificate where
  tauBall := tau0726
  contactCenter := center0726
  contactBall := contact0726
  work := work0726
  center_sq := center_sq0726
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0726.1
  jac_ok := checks0726.2.1
  accepted := checks0726.2.2

def tau0727 : RatBall :=
  ⟨⟨57/160, -29/160⟩, 3/320⟩
def center0727 : GaussianRat :=
  ⟨243609941/1000000000, -22312087/200000000⟩
def contact0727 : RatBall := localContactBall tau0727 center0727
def work0727 : RoundedTauEval :=
  evalTau precision tau0727 contact0727 logTwoBall

theorem center_sq0727 : (center0727.re : ℝ)^2 +
    (center0727.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0727]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0727 : work0727.theta.ok = true ∧
    work0727.jac.invOK = true ∧ acceptsUnitSq work0727.out = true := by decide +kernel

def cell0727 : CellCertificate where
  tauBall := tau0727
  contactCenter := center0727
  contactBall := contact0727
  work := work0727
  center_sq := center_sq0727
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0727.1
  jac_ok := checks0727.2.1
  accepted := checks0727.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090


