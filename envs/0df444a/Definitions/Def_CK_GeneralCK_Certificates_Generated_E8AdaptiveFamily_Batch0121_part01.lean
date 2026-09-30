-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0121_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0121_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:21:35.404064+00:00
-- url     : https://prove2.me/theorems/58f925ec-21c3-4541-9f0f-7ee5f1f15b32
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0121 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0121_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0971 : work0971.theta.ok = true ∧
    work0971.jac.invOK = true ∧ acceptsUnitSq work0971.out = true := by decide +kernel

def cell0971 : CellCertificate where
  tauBall := tau0971
  contactCenter := center0971
  contactBall := contact0971
  work := work0971
  center_sq := center_sq0971
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0971.1
  jac_ok := checks0971.2.1
  accepted := checks0971.2.2

def tau0972 : RatBall :=
  ⟨⟨-1/32, 51/160⟩, 3/320⟩
def center0972 : GaussianRat :=
  ⟨-24200917/1000000000, 228965453/1000000000⟩
def contact0972 : RatBall := localContactBall tau0972 center0972
def work0972 : RoundedTauEval :=
  evalTau precision tau0972 contact0972 logTwoBall

theorem center_sq0972 : (center0972.re : ℝ)^2 +
    (center0972.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0972]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0972 : work0972.theta.ok = true ∧
    work0972.jac.invOK = true ∧ acceptsUnitSq work0972.out = true := by decide +kernel

def cell0972 : CellCertificate where
  tauBall := tau0972
  contactCenter := center0972
  contactBall := contact0972
  work := work0972
  center_sq := center_sq0972
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0972.1
  jac_ok := checks0972.2.1
  accepted := checks0972.2.2

def tau0973 : RatBall :=
  ⟨⟨-3/160, 49/160⟩, 3/320⟩
def center0973 : GaussianRat :=
  ⟨-14395497/1000000000, 27438463/125000000⟩
def contact0973 : RatBall := localContactBall tau0973 center0973
def work0973 : RoundedTauEval :=
  evalTau precision tau0973 contact0973 logTwoBall

theorem center_sq0973 : (center0973.re : ℝ)^2 +
    (center0973.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0973]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0973 : work0973.theta.ok = true ∧
    work0973.jac.invOK = true ∧ acceptsUnitSq work0973.out = true := by decide +kernel

def cell0973 : CellCertificate where
  tauBall := tau0973
  contactCenter := center0973
  contactBall := contact0973
  work := work0973
  center_sq := center_sq0973
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0973.1
  jac_ok := checks0973.2.1
  accepted := checks0973.2.2

def tau0974 : RatBall :=
  ⟨⟨-1/160, 49/160⟩, 3/320⟩
def center0974 : GaussianRat :=
  ⟨-1199829/250000000, 109796019/500000000⟩
def contact0974 : RatBall := localContactBall tau0974 center0974
def work0974 : RoundedTauEval :=
  evalTau precision tau0974 contact0974 logTwoBall

theorem center_sq0974 : (center0974.re : ℝ)^2 +
    (center0974.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0974]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0974 : work0974.theta.ok = true ∧
    work0974.jac.invOK = true ∧ acceptsUnitSq work0974.out = true := by decide +kernel

def cell0974 : CellCertificate where
  tauBall := tau0974
  contactCenter := center0974
  contactBall := contact0974
  work := work0974
  center_sq := center_sq0974
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0974.1
  jac_ok := checks0974.2.1
  accepted := checks0974.2.2

def tau0975 : RatBall :=
  ⟨⟨-3/160, 51/160⟩, 3/320⟩
def center0975 : GaussianRat :=
  ⟨-581027/40000000, 57285979/250000000⟩
def contact0975 : RatBall := localContactBall tau0975 center0975

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121


