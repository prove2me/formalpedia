-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0060
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0060
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:59:30.228774+00:00
-- url     : https://prove2.me/theorems/6f2eecd6-4b13-43c6-8ac3-1580c5eb3dc7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0060.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0060_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work0485 : RoundedTauEval :=
  evalTau precision tau0485 contact0485 logTwoBall

theorem center_sq0485 : (center0485.re : ℝ)^2 +
    (center0485.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0485]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0485 : work0485.theta.ok = true ∧
    work0485.jac.invOK = true ∧ acceptsUnitSq work0485.out = true := by decide +kernel

def cell0485 : CellCertificate where
  tauBall := tau0485
  contactCenter := center0485
  contactBall := contact0485
  work := work0485
  center_sq := center_sq0485
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0485.1
  jac_ok := checks0485.2.1
  accepted := checks0485.2.2

def tau0486 : RatBall :=
  ⟨⟨-11/32, -31/160⟩, 3/320⟩
def center0486 : GaussianRat :=
  ⟨-47354053/200000000, -30090849/250000000⟩
def contact0486 : RatBall := localContactBall tau0486 center0486
def work0486 : RoundedTauEval :=
  evalTau precision tau0486 contact0486 logTwoBall

theorem center_sq0486 : (center0486.re : ℝ)^2 +
    (center0486.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0486]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0486 : work0486.theta.ok = true ∧
    work0486.jac.invOK = true ∧ acceptsUnitSq work0486.out = true := by decide +kernel

def cell0486 : CellCertificate where
  tauBall := tau0486
  contactCenter := center0486
  contactBall := contact0486
  work := work0486
  center_sq := center_sq0486
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0486.1
  jac_ok := checks0486.2.1
  accepted := checks0486.2.2

def tau0487 : RatBall :=
  ⟨⟨-53/160, -31/160⟩, 3/320⟩
def center0487 : GaussianRat :=
  ⟨-114433899/500000000, -30340451/250000000⟩
def contact0487 : RatBall := localContactBall tau0487 center0487
def work0487 : RoundedTauEval :=
  evalTau precision tau0487 contact0487 logTwoBall

theorem center_sq0487 : (center0487.re : ℝ)^2 +
    (center0487.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0487]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0487 : work0487.theta.ok = true ∧
    work0487.jac.invOK = true ∧ acceptsUnitSq work0487.out = true := by decide +kernel

def cell0487 : CellCertificate where
  tauBall := tau0487
  contactCenter := center0487
  contactBall := contact0487
  work := work0487
  center_sq := center_sq0487
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0487.1
  jac_ok := checks0487.2.1
  accepted := checks0487.2.2

def cells : List CellCertificate := [cell0480, cell0481, cell0482, cell0483, cell0484, cell0485, cell0486, cell0487]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060


