-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0096_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0096_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:14:48.496706+00:00
-- url     : https://prove2.me/theorems/fde61c00-8ed7-4c3f-9a78-fdb62a359827
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0096 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0768 : RatBall :=
  ⟨⟨61/160, -7/160⟩, 3/320⟩
def center0768 : GaussianRat :=
  ⟨252422417/1000000000, -13171007/500000000⟩
def contact0768 : RatBall := localContactBall tau0768 center0768
def work0768 : RoundedTauEval :=
  evalTau precision tau0768 contact0768 logTwoBall

theorem center_sq0768 : (center0768.re : ℝ)^2 +
    (center0768.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0768]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0768 : work0768.theta.ok = true ∧
    work0768.jac.invOK = true ∧ acceptsUnitSq work0768.out = true := by decide +kernel

def cell0768 : CellCertificate where
  tauBall := tau0768
  contactCenter := center0768
  contactBall := contact0768
  work := work0768
  center_sq := center_sq0768
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0768.1
  jac_ok := checks0768.2.1
  accepted := checks0768.2.2

def tau0769 : RatBall :=
  ⟨⟨63/160, -7/160⟩, 3/320⟩
def center0769 : GaussianRat :=
  ⟨64979987/250000000, -3263977/125000000⟩
def contact0769 : RatBall := localContactBall tau0769 center0769
def work0769 : RoundedTauEval :=
  evalTau precision tau0769 contact0769 logTwoBall

theorem center_sq0769 : (center0769.re : ℝ)^2 +
    (center0769.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0769]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0769 : work0769.theta.ok = true ∧
    work0769.jac.invOK = true ∧ acceptsUnitSq work0769.out = true := by decide +kernel

def cell0769 : CellCertificate where
  tauBall := tau0769
  contactCenter := center0769
  contactBall := contact0769
  work := work0769
  center_sq := center_sq0769
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0769.1
  jac_ok := checks0769.2.1
  accepted := checks0769.2.2

def tau0770 : RatBall :=
  ⟨⟨61/160, -1/32⟩, 3/320⟩
def center0770 : GaussianRat :=
  ⟨25222673/100000000, -18813147/1000000000⟩
def contact0770 : RatBall := localContactBall tau0770 center0770
def work0770 : RoundedTauEval :=
  evalTau precision tau0770 contact0770 logTwoBall

theorem center_sq0770 : (center0770.re : ℝ)^2 +
    (center0770.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0770]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0770 : work0770.theta.ok = true ∧
    work0770.jac.invOK = true ∧ acceptsUnitSq work0770.out = true := by decide +kernel

def cell0770 : CellCertificate where
  tauBall := tau0770
  contactCenter := center0770
  contactBall := contact0770
  work := work0770
  center_sq := center_sq0770
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0770.1
  jac_ok := checks0770.2.1
  accepted := checks0770.2.2

def tau0771 : RatBall :=
  ⟨⟨63/160, -1/32⟩, 3/320⟩
def center0771 : GaussianRat :=
  ⟨259721291/1000000000, -466223/25000000⟩
def contact0771 : RatBall := localContactBall tau0771 center0771
def work0771 : RoundedTauEval :=
  evalTau precision tau0771 contact0771 logTwoBall

theorem center_sq0771 : (center0771.re : ℝ)^2 +
    (center0771.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0771]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096


