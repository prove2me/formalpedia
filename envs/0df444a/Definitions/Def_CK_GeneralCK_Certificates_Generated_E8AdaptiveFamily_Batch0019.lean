-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0019
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0019
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:09:06.462966+00:00
-- url     : https://prove2.me/theorems/aaf7a2ff-d999-4666-8b11-54d2ae367ad4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0019.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0019_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0156 : (center0156.re : ℝ)^2 +
    (center0156.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0156]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0156 : work0156.theta.ok = true ∧
    work0156.jac.invOK = true ∧ acceptsUnitSq work0156.out = true := by decide +kernel

def cell0156 : CellCertificate where
  tauBall := tau0156
  contactCenter := center0156
  contactBall := contact0156
  work := work0156
  center_sq := center_sq0156
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0156.1
  jac_ok := checks0156.2.1
  accepted := checks0156.2.2

def tau0157 : RatBall :=
  ⟨⟨13/80, -11/80⟩, 3/160⟩
def center0157 : GaussianRat :=
  ⟨22751869/200000000, -46647191/500000000⟩
def contact0157 : RatBall := localContactBall tau0157 center0157
def work0157 : RoundedTauEval :=
  evalTau precision tau0157 contact0157 logTwoBall

theorem center_sq0157 : (center0157.re : ℝ)^2 +
    (center0157.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0157]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0157 : work0157.theta.ok = true ∧
    work0157.jac.invOK = true ∧ acceptsUnitSq work0157.out = true := by decide +kernel

def cell0157 : CellCertificate where
  tauBall := tau0157
  contactCenter := center0157
  contactBall := contact0157
  work := work0157
  center_sq := center_sq0157
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0157.1
  jac_ok := checks0157.2.1
  accepted := checks0157.2.2

def tau0158 : RatBall :=
  ⟨⟨3/16, -11/80⟩, 3/160⟩
def center0158 : GaussianRat :=
  ⟨130837509/1000000000, -92449971/1000000000⟩
def contact0158 : RatBall := localContactBall tau0158 center0158
def work0158 : RoundedTauEval :=
  evalTau precision tau0158 contact0158 logTwoBall

theorem center_sq0158 : (center0158.re : ℝ)^2 +
    (center0158.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0158]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0158 : work0158.theta.ok = true ∧
    work0158.jac.invOK = true ∧ acceptsUnitSq work0158.out = true := by decide +kernel

def cell0158 : CellCertificate where
  tauBall := tau0158
  contactCenter := center0158
  contactBall := contact0158
  work := work0158
  center_sq := center_sq0158
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0158.1
  jac_ok := checks0158.2.1
  accepted := checks0158.2.2

def tau0159 : RatBall :=
  ⟨⟨13/80, -9/80⟩, 3/160⟩
def center0159 : GaussianRat :=
  ⟨56522129/500000000, -76186323/1000000000⟩
def contact0159 : RatBall := localContactBall tau0159 center0159
def work0159 : RoundedTauEval :=
  evalTau precision tau0159 contact0159 logTwoBall

theorem center_sq0159 : (center0159.re : ℝ)^2 +
    (center0159.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0159]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0159 : work0159.theta.ok = true ∧
    work0159.jac.invOK = true ∧ acceptsUnitSq work0159.out = true := by decide +kernel

def cell0159 : CellCertificate where
  tauBall := tau0159
  contactCenter := center0159
  contactBall := contact0159
  work := work0159
  center_sq := center_sq0159
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0159.1
  jac_ok := checks0159.2.1
  accepted := checks0159.2.2

def cells : List CellCertificate := [cell0152, cell0153, cell0154, cell0155, cell0156, cell0157, cell0158, cell0159]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019


