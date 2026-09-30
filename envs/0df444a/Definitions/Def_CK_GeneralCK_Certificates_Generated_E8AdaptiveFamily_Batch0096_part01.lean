-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0096_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0096_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:10:07.816747+00:00
-- url     : https://prove2.me/theorems/ec0a2092-fc79-426a-a42e-c04579c49bf0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0096 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0096_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0771 : work0771.theta.ok = true ∧
    work0771.jac.invOK = true ∧ acceptsUnitSq work0771.out = true := by decide +kernel

def cell0771 : CellCertificate where
  tauBall := tau0771
  contactCenter := center0771
  contactBall := contact0771
  work := work0771
  center_sq := center_sq0771
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0771.1
  jac_ok := checks0771.2.1
  accepted := checks0771.2.2

def tau0772 : RatBall :=
  ⟨⟨-63/160, 1/32⟩, 3/320⟩
def center0772 : GaussianRat :=
  ⟨-259721291/1000000000, 466223/25000000⟩
def contact0772 : RatBall := localContactBall tau0772 center0772
def work0772 : RoundedTauEval :=
  evalTau precision tau0772 contact0772 logTwoBall

theorem center_sq0772 : (center0772.re : ℝ)^2 +
    (center0772.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0772]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0772 : work0772.theta.ok = true ∧
    work0772.jac.invOK = true ∧ acceptsUnitSq work0772.out = true := by decide +kernel

def cell0772 : CellCertificate where
  tauBall := tau0772
  contactCenter := center0772
  contactBall := contact0772
  work := work0772
  center_sq := center_sq0772
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0772.1
  jac_ok := checks0772.2.1
  accepted := checks0772.2.2

def tau0773 : RatBall :=
  ⟨⟨-61/160, 1/32⟩, 3/320⟩
def center0773 : GaussianRat :=
  ⟨-25222673/100000000, 18813147/1000000000⟩
def contact0773 : RatBall := localContactBall tau0773 center0773
def work0773 : RoundedTauEval :=
  evalTau precision tau0773 contact0773 logTwoBall

theorem center_sq0773 : (center0773.re : ℝ)^2 +
    (center0773.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0773]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0773 : work0773.theta.ok = true ∧
    work0773.jac.invOK = true ∧ acceptsUnitSq work0773.out = true := by decide +kernel

def cell0773 : CellCertificate where
  tauBall := tau0773
  contactCenter := center0773
  contactBall := contact0773
  work := work0773
  center_sq := center_sq0773
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0773.1
  jac_ok := checks0773.2.1
  accepted := checks0773.2.2

def tau0774 : RatBall :=
  ⟨⟨-63/160, 7/160⟩, 3/320⟩
def center0774 : GaussianRat :=
  ⟨-64979987/250000000, 3263977/125000000⟩
def contact0774 : RatBall := localContactBall tau0774 center0774
def work0774 : RoundedTauEval :=
  evalTau precision tau0774 contact0774 logTwoBall

theorem center_sq0774 : (center0774.re : ℝ)^2 +
    (center0774.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0774]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0774 : work0774.theta.ok = true ∧
    work0774.jac.invOK = true ∧ acceptsUnitSq work0774.out = true := by decide +kernel

def cell0774 : CellCertificate where
  tauBall := tau0774
  contactCenter := center0774
  contactBall := contact0774
  work := work0774
  center_sq := center_sq0774
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0774.1
  jac_ok := checks0774.2.1
  accepted := checks0774.2.2

def tau0775 : RatBall :=
  ⟨⟨-61/160, 7/160⟩, 3/320⟩
def center0775 : GaussianRat :=
  ⟨-252422417/1000000000, 13171007/500000000⟩
def contact0775 : RatBall := localContactBall tau0775 center0775

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096


