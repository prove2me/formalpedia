-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0071_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0071_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:09:42.079584+00:00
-- url     : https://prove2.me/theorems/44738455-0b80-4db6-ba69-fed4cf340b7f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0071 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0568 : RatBall :=
  ⟨⟨3/160, -51/160⟩, 3/320⟩
def center0568 : GaussianRat :=
  ⟨581027/40000000, -57285979/250000000⟩
def contact0568 : RatBall := localContactBall tau0568 center0568
def work0568 : RoundedTauEval :=
  evalTau precision tau0568 contact0568 logTwoBall

theorem center_sq0568 : (center0568.re : ℝ)^2 +
    (center0568.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0568]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0568 : work0568.theta.ok = true ∧
    work0568.jac.invOK = true ∧ acceptsUnitSq work0568.out = true := by decide +kernel

def cell0568 : CellCertificate where
  tauBall := tau0568
  contactCenter := center0568
  contactBall := contact0568
  work := work0568
  center_sq := center_sq0568
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0568.1
  jac_ok := checks0568.2.1
  accepted := checks0568.2.2

def tau0569 : RatBall :=
  ⟨⟨1/160, -49/160⟩, 3/320⟩
def center0569 : GaussianRat :=
  ⟨1199829/250000000, -109796019/500000000⟩
def contact0569 : RatBall := localContactBall tau0569 center0569
def work0569 : RoundedTauEval :=
  evalTau precision tau0569 contact0569 logTwoBall

theorem center_sq0569 : (center0569.re : ℝ)^2 +
    (center0569.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0569]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0569 : work0569.theta.ok = true ∧
    work0569.jac.invOK = true ∧ acceptsUnitSq work0569.out = true := by decide +kernel

def cell0569 : CellCertificate where
  tauBall := tau0569
  contactCenter := center0569
  contactBall := contact0569
  work := work0569
  center_sq := center_sq0569
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0569.1
  jac_ok := checks0569.2.1
  accepted := checks0569.2.2

def tau0570 : RatBall :=
  ⟨⟨3/160, -49/160⟩, 3/320⟩
def center0570 : GaussianRat :=
  ⟨14395497/1000000000, -27438463/125000000⟩
def contact0570 : RatBall := localContactBall tau0570 center0570
def work0570 : RoundedTauEval :=
  evalTau precision tau0570 contact0570 logTwoBall

theorem center_sq0570 : (center0570.re : ℝ)^2 +
    (center0570.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0570]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0570 : work0570.theta.ok = true ∧
    work0570.jac.invOK = true ∧ acceptsUnitSq work0570.out = true := by decide +kernel

def cell0570 : CellCertificate where
  tauBall := tau0570
  contactCenter := center0570
  contactBall := contact0570
  work := work0570
  center_sq := center_sq0570
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0570.1
  jac_ok := checks0570.2.1
  accepted := checks0570.2.2

def tau0571 : RatBall :=
  ⟨⟨1/32, -51/160⟩, 3/320⟩
def center0571 : GaussianRat :=
  ⟨24200917/1000000000, -228965453/1000000000⟩
def contact0571 : RatBall := localContactBall tau0571 center0571
def work0571 : RoundedTauEval :=
  evalTau precision tau0571 contact0571 logTwoBall

theorem center_sq0571 : (center0571.re : ℝ)^2 +
    (center0571.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0571]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0571 : work0571.theta.ok = true ∧
    work0571.jac.invOK = true ∧ acceptsUnitSq work0571.out = true := by decide +kernel

def cell0571 : CellCertificate where
  tauBall := tau0571
  contactCenter := center0571
  contactBall := contact0571
  work := work0571
  center_sq := center_sq0571
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0571.1
  jac_ok := checks0571.2.1
  accepted := checks0571.2.2

def tau0572 : RatBall :=
  ⟨⟨7/160, -51/160⟩, 3/320⟩
def center0572 : GaussianRat :=
  ⟨1693169/50000000, -228698347/1000000000⟩
def contact0572 : RatBall := localContactBall tau0572 center0572
def work0572 : RoundedTauEval :=
  evalTau precision tau0572 contact0572 logTwoBall

theorem center_sq0572 : (center0572.re : ℝ)^2 +
    (center0572.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0572]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0572 : work0572.theta.ok = true ∧
    work0572.jac.invOK = true ∧ acceptsUnitSq work0572.out = true := by decide +kernel

def cell0572 : CellCertificate where
  tauBall := tau0572
  contactCenter := center0572
  contactBall := contact0572
  work := work0572
  center_sq := center_sq0572
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0572.1
  jac_ok := checks0572.2.1
  accepted := checks0572.2.2

def tau0573 : RatBall :=
  ⟨⟨1/32, -49/160⟩, 3/320⟩
def center0573 : GaussianRat :=
  ⟨2398433/100000000, -219339251/1000000000⟩
def contact0573 : RatBall := localContactBall tau0573 center0573
def work0573 : RoundedTauEval :=
  evalTau precision tau0573 contact0573 logTwoBall

theorem center_sq0573 : (center0573.re : ℝ)^2 +
    (center0573.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0573]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0573 : work0573.theta.ok = true ∧
    work0573.jac.invOK = true ∧ acceptsUnitSq work0573.out = true := by decide +kernel

def cell0573 : CellCertificate where
  tauBall := tau0573
  contactCenter := center0573
  contactBall := contact0573
  work := work0573
  center_sq := center_sq0573
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0573.1
  jac_ok := checks0573.2.1
  accepted := checks0573.2.2

def tau0574 : RatBall :=
  ⟨⟨7/160, -49/160⟩, 3/320⟩
def center0574 : GaussianRat :=
  ⟨16780473/500000000, -219087113/1000000000⟩
def contact0574 : RatBall := localContactBall tau0574 center0574
def work0574 : RoundedTauEval :=
  evalTau precision tau0574 contact0574 logTwoBall

theorem center_sq0574 : (center0574.re : ℝ)^2 +
    (center0574.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0574]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0574 : work0574.theta.ok = true ∧
    work0574.jac.invOK = true ∧ acceptsUnitSq work0574.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071


