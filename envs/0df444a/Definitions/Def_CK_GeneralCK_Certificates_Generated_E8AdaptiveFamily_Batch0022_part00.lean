-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0022_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0022_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:06:52.477972+00:00
-- url     : https://prove2.me/theorems/bd8f9cfc-c40e-4193-a6dd-91e09b4827fc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0022 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0176 : RatBall :=
  ⟨⟨17/80, -1/16⟩, 3/160⟩
def center0176 : GaussianRat :=
  ⟨29119789/200000000, -10355411/250000000⟩
def contact0176 : RatBall := localContactBall tau0176 center0176
def work0176 : RoundedTauEval :=
  evalTau precision tau0176 contact0176 logTwoBall

theorem center_sq0176 : (center0176.re : ℝ)^2 +
    (center0176.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0176]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0176 : work0176.theta.ok = true ∧
    work0176.jac.invOK = true ∧ acceptsUnitSq work0176.out = true := by decide +kernel

def cell0176 : CellCertificate where
  tauBall := tau0176
  contactCenter := center0176
  contactBall := contact0176
  work := work0176
  center_sq := center_sq0176
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0176.1
  jac_ok := checks0176.2.1
  accepted := checks0176.2.2

def tau0177 : RatBall :=
  ⟨⟨19/80, -1/16⟩, 3/160⟩
def center0177 : GaussianRat :=
  ⟨81055451/500000000, -40960501/1000000000⟩
def contact0177 : RatBall := localContactBall tau0177 center0177
def work0177 : RoundedTauEval :=
  evalTau precision tau0177 contact0177 logTwoBall

theorem center_sq0177 : (center0177.re : ℝ)^2 +
    (center0177.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0177]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0177 : work0177.theta.ok = true ∧
    work0177.jac.invOK = true ∧ acceptsUnitSq work0177.out = true := by decide +kernel

def cell0177 : CellCertificate where
  tauBall := tau0177
  contactCenter := center0177
  contactBall := contact0177
  work := work0177
  center_sq := center_sq0177
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0177.1
  jac_ok := checks0177.2.1
  accepted := checks0177.2.2

def tau0178 : RatBall :=
  ⟨⟨21/80, -7/80⟩, 3/160⟩
def center0178 : GaussianRat :=
  ⟨17905297/100000000, -5669463/100000000⟩
def contact0178 : RatBall := localContactBall tau0178 center0178
def work0178 : RoundedTauEval :=
  evalTau precision tau0178 contact0178 logTwoBall

theorem center_sq0178 : (center0178.re : ℝ)^2 +
    (center0178.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0178]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0178 : work0178.theta.ok = true ∧
    work0178.jac.invOK = true ∧ acceptsUnitSq work0178.out = true := by decide +kernel

def cell0178 : CellCertificate where
  tauBall := tau0178
  contactCenter := center0178
  contactBall := contact0178
  work := work0178
  center_sq := center_sq0178
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0178.1
  jac_ok := checks0178.2.1
  accepted := checks0178.2.2

def tau0179 : RatBall :=
  ⟨⟨23/80, -7/80⟩, 3/160⟩
def center0179 : GaussianRat :=
  ⟨195201217/1000000000, -13984569/250000000⟩
def contact0179 : RatBall := localContactBall tau0179 center0179
def work0179 : RoundedTauEval :=
  evalTau precision tau0179 contact0179 logTwoBall

theorem center_sq0179 : (center0179.re : ℝ)^2 +
    (center0179.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0179]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0179 : work0179.theta.ok = true ∧
    work0179.jac.invOK = true ∧ acceptsUnitSq work0179.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022


