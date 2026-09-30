-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0055_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0055_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:55:34.258276+00:00
-- url     : https://prove2.me/theorems/d5521df4-a3c9-449a-aae5-02b809dedca1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0055 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0055_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0443 : work0443.theta.ok = true ∧
    work0443.jac.invOK = true ∧ acceptsUnitSq work0443.out = true := by decide +kernel

def cell0443 : CellCertificate where
  tauBall := tau0443
  contactCenter := center0443
  contactBall := contact0443
  work := work0443
  center_sq := center_sq0443
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0443.1
  jac_ok := checks0443.2.1
  accepted := checks0443.2.2

def tau0444 : RatBall :=
  ⟨⟨-29/160, -41/160⟩, 3/320⟩
def center0444 : GaussianRat :=
  ⟨-132776829/1000000000, -35027183/200000000⟩
def contact0444 : RatBall := localContactBall tau0444 center0444
def work0444 : RoundedTauEval :=
  evalTau precision tau0444 contact0444 logTwoBall

theorem center_sq0444 : (center0444.re : ℝ)^2 +
    (center0444.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0444]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0444 : work0444.theta.ok = true ∧
    work0444.jac.invOK = true ∧ acceptsUnitSq work0444.out = true := by decide +kernel

def cell0444 : CellCertificate where
  tauBall := tau0444
  contactCenter := center0444
  contactBall := contact0444
  work := work0444
  center_sq := center_sq0444
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0444.1
  jac_ok := checks0444.2.1
  accepted := checks0444.2.2

def tau0445 : RatBall :=
  ⟨⟨-27/160, -43/160⟩, 3/320⟩
def center0445 : GaussianRat :=
  ⟨-1948873/15625000, -92480083/500000000⟩
def contact0445 : RatBall := localContactBall tau0445 center0445
def work0445 : RoundedTauEval :=
  evalTau precision tau0445 contact0445 logTwoBall

theorem center_sq0445 : (center0445.re : ℝ)^2 +
    (center0445.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0445]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0445 : work0445.theta.ok = true ∧
    work0445.jac.invOK = true ∧ acceptsUnitSq work0445.out = true := by decide +kernel

def cell0445 : CellCertificate where
  tauBall := tau0445
  contactCenter := center0445
  contactBall := contact0445
  work := work0445
  center_sq := center_sq0445
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0445.1
  jac_ok := checks0445.2.1
  accepted := checks0445.2.2

def tau0446 : RatBall :=
  ⟨⟨-5/32, -43/160⟩, 3/320⟩
def center0446 : GaussianRat :=
  ⟨-57855523/500000000, -185818573/1000000000⟩
def contact0446 : RatBall := localContactBall tau0446 center0446
def work0446 : RoundedTauEval :=
  evalTau precision tau0446 contact0446 logTwoBall

theorem center_sq0446 : (center0446.re : ℝ)^2 +
    (center0446.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0446]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0446 : work0446.theta.ok = true ∧
    work0446.jac.invOK = true ∧ acceptsUnitSq work0446.out = true := by decide +kernel

def cell0446 : CellCertificate where
  tauBall := tau0446
  contactCenter := center0446
  contactBall := contact0446
  work := work0446
  center_sq := center_sq0446
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0446.1
  jac_ok := checks0446.2.1
  accepted := checks0446.2.2

def tau0447 : RatBall :=
  ⟨⟨-27/160, -41/160⟩, 3/320⟩
def center0447 : GaussianRat :=
  ⟨-123867137/1000000000, -21999637/125000000⟩
def contact0447 : RatBall := localContactBall tau0447 center0447

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055


