-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0090_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0090_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:12:33.488466+00:00
-- url     : https://prove2.me/theorems/0a0615cf-1cb4-49f9-be0b-b38f67e8ad56
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0090 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0720 : RatBall :=
  ⟨⟨51/160, -27/160⟩, 3/320⟩
def center0720 : GaussianRat :=
  ⟨219098349/1000000000, -53182749/500000000⟩
def contact0720 : RatBall := localContactBall tau0720 center0720
def work0720 : RoundedTauEval :=
  evalTau precision tau0720 contact0720 logTwoBall

theorem center_sq0720 : (center0720.re : ℝ)^2 +
    (center0720.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0720]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0720 : work0720.theta.ok = true ∧
    work0720.jac.invOK = true ∧ acceptsUnitSq work0720.out = true := by decide +kernel

def cell0720 : CellCertificate where
  tauBall := tau0720
  contactCenter := center0720
  contactBall := contact0720
  work := work0720
  center_sq := center_sq0720
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0720.1
  jac_ok := checks0720.2.1
  accepted := checks0720.2.2

def tau0721 : RatBall :=
  ⟨⟨49/160, -5/32⟩, 3/320⟩
def center0721 : GaussianRat :=
  ⟨52580197/250000000, -1239543/12500000⟩
def contact0721 : RatBall := localContactBall tau0721 center0721
def work0721 : RoundedTauEval :=
  evalTau precision tau0721 contact0721 logTwoBall

theorem center_sq0721 : (center0721.re : ℝ)^2 +
    (center0721.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0721]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0721 : work0721.theta.ok = true ∧
    work0721.jac.invOK = true ∧ acceptsUnitSq work0721.out = true := by decide +kernel

def cell0721 : CellCertificate where
  tauBall := tau0721
  contactCenter := center0721
  contactBall := contact0721
  work := work0721
  center_sq := center_sq0721
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0721.1
  jac_ok := checks0721.2.1
  accepted := checks0721.2.2

def tau0722 : RatBall :=
  ⟨⟨51/160, -5/32⟩, 3/320⟩
def center0722 : GaussianRat :=
  ⟨5457529/25000000, -49204231/500000000⟩
def contact0722 : RatBall := localContactBall tau0722 center0722
def work0722 : RoundedTauEval :=
  evalTau precision tau0722 contact0722 logTwoBall

theorem center_sq0722 : (center0722.re : ℝ)^2 +
    (center0722.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0722]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0722 : work0722.theta.ok = true ∧
    work0722.jac.invOK = true ∧ acceptsUnitSq work0722.out = true := by decide +kernel

def cell0722 : CellCertificate where
  tauBall := tau0722
  contactCenter := center0722
  contactBall := contact0722
  work := work0722
  center_sq := center_sq0722
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0722.1
  jac_ok := checks0722.2.1
  accepted := checks0722.2.2

def tau0723 : RatBall :=
  ⟨⟨53/160, -27/160⟩, 3/320⟩
def center0723 : GaussianRat :=
  ⟨113515613/500000000, -13190697/125000000⟩
def contact0723 : RatBall := localContactBall tau0723 center0723
def work0723 : RoundedTauEval :=
  evalTau precision tau0723 contact0723 logTwoBall

theorem center_sq0723 : (center0723.re : ℝ)^2 +
    (center0723.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0723]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0723 : work0723.theta.ok = true ∧
    work0723.jac.invOK = true ∧ acceptsUnitSq work0723.out = true := by decide +kernel

def cell0723 : CellCertificate where
  tauBall := tau0723
  contactCenter := center0723
  contactBall := contact0723
  work := work0723
  center_sq := center_sq0723
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0723.1
  jac_ok := checks0723.2.1
  accepted := checks0723.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090


