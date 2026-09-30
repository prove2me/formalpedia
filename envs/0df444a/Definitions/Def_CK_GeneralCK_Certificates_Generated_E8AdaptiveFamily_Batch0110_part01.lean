-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0110_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0110_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:08:52.420449+00:00
-- url     : https://prove2.me/theorems/43ad7dc0-844e-47a5-b1e6-08165c88e710
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0110 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0110_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work0882 : RoundedTauEval :=
  evalTau precision tau0882 contact0882 logTwoBall

theorem center_sq0882 : (center0882.re : ℝ)^2 +
    (center0882.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0882]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0882 : work0882.theta.ok = true ∧
    work0882.jac.invOK = true ∧ acceptsUnitSq work0882.out = true := by decide +kernel

def cell0882 : CellCertificate where
  tauBall := tau0882
  contactCenter := center0882
  contactBall := contact0882
  work := work0882
  center_sq := center_sq0882
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0882.1
  jac_ok := checks0882.2.1
  accepted := checks0882.2.2

def tau0883 : RatBall :=
  ⟨⟨-33/160, 37/160⟩, 3/320⟩
def center0883 : GaussianRat :=
  ⟨-148574359/1000000000, 31163137/200000000⟩
def contact0883 : RatBall := localContactBall tau0883 center0883
def work0883 : RoundedTauEval :=
  evalTau precision tau0883 contact0883 logTwoBall

theorem center_sq0883 : (center0883.re : ℝ)^2 +
    (center0883.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0883]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0883 : work0883.theta.ok = true ∧
    work0883.jac.invOK = true ∧ acceptsUnitSq work0883.out = true := by decide +kernel

def cell0883 : CellCertificate where
  tauBall := tau0883
  contactCenter := center0883
  contactBall := contact0883
  work := work0883
  center_sq := center_sq0883
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0883.1
  jac_ok := checks0883.2.1
  accepted := checks0883.2.2

def tau0884 : RatBall :=
  ⟨⟨-7/32, 39/160⟩, 3/320⟩
def center0884 : GaussianRat :=
  ⟨-9885359/62500000, 81782823/500000000⟩
def contact0884 : RatBall := localContactBall tau0884 center0884
def work0884 : RoundedTauEval :=
  evalTau precision tau0884 contact0884 logTwoBall

theorem center_sq0884 : (center0884.re : ℝ)^2 +
    (center0884.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0884]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0884 : work0884.theta.ok = true ∧
    work0884.jac.invOK = true ∧ acceptsUnitSq work0884.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110


