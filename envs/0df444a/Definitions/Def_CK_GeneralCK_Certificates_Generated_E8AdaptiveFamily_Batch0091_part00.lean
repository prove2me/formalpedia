-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0091_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0091_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:24:21.063007+00:00
-- url     : https://prove2.me/theorems/c0f72458-b4a0-445d-a28e-0136f94a2e5d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0091 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0728 : RatBall :=
  ⟨⟨57/160, -27/160⟩, 3/320⟩
def center0728 : GaussianRat :=
  ⟨242691133/1000000000, -103792249/1000000000⟩
def contact0728 : RatBall := localContactBall tau0728 center0728
def work0728 : RoundedTauEval :=
  evalTau precision tau0728 contact0728 logTwoBall

theorem center_sq0728 : (center0728.re : ℝ)^2 +
    (center0728.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0728]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0728 : work0728.theta.ok = true ∧
    work0728.jac.invOK = true ∧ acceptsUnitSq work0728.out = true := by decide +kernel

def cell0728 : CellCertificate where
  tauBall := tau0728
  contactCenter := center0728
  contactBall := contact0728
  work := work0728
  center_sq := center_sq0728
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0728.1
  jac_ok := checks0728.2.1
  accepted := checks0728.2.2

def tau0729 : RatBall :=
  ⟨⟨59/160, -27/160⟩, 3/320⟩
def center0729 : GaussianRat :=
  ⟨6260393/25000000, -51450627/500000000⟩
def contact0729 : RatBall := localContactBall tau0729 center0729
def work0729 : RoundedTauEval :=
  evalTau precision tau0729 contact0729 logTwoBall

theorem center_sq0729 : (center0729.re : ℝ)^2 +
    (center0729.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0729]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0729 : work0729.theta.ok = true ∧
    work0729.jac.invOK = true ∧ acceptsUnitSq work0729.out = true := by decide +kernel

def cell0729 : CellCertificate where
  tauBall := tau0729
  contactCenter := center0729
  contactBall := contact0729
  work := work0729
  center_sq := center_sq0729
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0729.1
  jac_ok := checks0729.2.1
  accepted := checks0729.2.2

def tau0730 : RatBall :=
  ⟨⟨57/160, -5/32⟩, 3/320⟩
def center0730 : GaussianRat :=
  ⟨7557593/31250000, -96039881/1000000000⟩
def contact0730 : RatBall := localContactBall tau0730 center0730
def work0730 : RoundedTauEval :=
  evalTau precision tau0730 contact0730 logTwoBall

theorem center_sq0730 : (center0730.re : ℝ)^2 +
    (center0730.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0730]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0730 : work0730.theta.ok = true ∧
    work0730.jac.invOK = true ∧ acceptsUnitSq work0730.out = true := by decide +kernel

def cell0730 : CellCertificate where
  tauBall := tau0730
  contactCenter := center0730
  contactBall := contact0730
  work := work0730
  center_sq := center_sq0730
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0730.1
  jac_ok := checks0730.2.1
  accepted := checks0730.2.2

def tau0731 : RatBall :=
  ⟨⟨59/160, -5/32⟩, 3/320⟩
def center0731 : GaussianRat :=
  ⟨1996423/8000000, -19043899/200000000⟩
def contact0731 : RatBall := localContactBall tau0731 center0731
def work0731 : RoundedTauEval :=
  evalTau precision tau0731 contact0731 logTwoBall

theorem center_sq0731 : (center0731.re : ℝ)^2 +
    (center0731.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0731]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0731 : work0731.theta.ok = true ∧
    work0731.jac.invOK = true ∧ acceptsUnitSq work0731.out = true := by decide +kernel

def cell0731 : CellCertificate where
  tauBall := tau0731
  contactCenter := center0731
  contactBall := contact0731
  work := work0731
  center_sq := center_sq0731
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0731.1
  jac_ok := checks0731.2.1
  accepted := checks0731.2.2

def tau0732 : RatBall :=
  ⟨⟨49/160, -23/160⟩, 3/320⟩
def center0732 : GaussianRat :=
  ⟨209607093/1000000000, -22790011/250000000⟩
def contact0732 : RatBall := localContactBall tau0732 center0732
def work0732 : RoundedTauEval :=
  evalTau precision tau0732 contact0732 logTwoBall

theorem center_sq0732 : (center0732.re : ℝ)^2 +
    (center0732.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0732]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0732 : work0732.theta.ok = true ∧
    work0732.jac.invOK = true ∧ acceptsUnitSq work0732.out = true := by decide +kernel

def cell0732 : CellCertificate where
  tauBall := tau0732
  contactCenter := center0732
  contactBall := contact0732
  work := work0732
  center_sq := center_sq0732
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0732.1
  jac_ok := checks0732.2.1
  accepted := checks0732.2.2

def tau0733 : RatBall :=
  ⟨⟨51/160, -23/160⟩, 3/320⟩
def center0733 : GaussianRat :=
  ⟨6799051/31250000, -90469443/1000000000⟩
def contact0733 : RatBall := localContactBall tau0733 center0733
def work0733 : RoundedTauEval :=
  evalTau precision tau0733 contact0733 logTwoBall

theorem center_sq0733 : (center0733.re : ℝ)^2 +
    (center0733.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0733]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091


