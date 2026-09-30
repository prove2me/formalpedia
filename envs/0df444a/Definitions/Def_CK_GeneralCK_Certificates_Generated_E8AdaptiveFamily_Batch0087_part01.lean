-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0087_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0087_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:16:54.632501+00:00
-- url     : https://prove2.me/theorems/d3e5c711-6d0b-43e3-992b-a8c781aaa474
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0087 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0087_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0699 : RatBall :=
  ⟨⟨41/160, -31/160⟩, 3/320⟩
def center0699 : GaussianRat :=
  ⟨36003433/200000000, -3171591/25000000⟩
def contact0699 : RatBall := localContactBall tau0699 center0699
def work0699 : RoundedTauEval :=
  evalTau precision tau0699 contact0699 logTwoBall

theorem center_sq0699 : (center0699.re : ℝ)^2 +
    (center0699.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0699]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0699 : work0699.theta.ok = true ∧
    work0699.jac.invOK = true ∧ acceptsUnitSq work0699.out = true := by decide +kernel

def cell0699 : CellCertificate where
  tauBall := tau0699
  contactCenter := center0699
  contactBall := contact0699
  work := work0699
  center_sq := center_sq0699
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0699.1
  jac_ok := checks0699.2.1
  accepted := checks0699.2.2

def tau0700 : RatBall :=
  ⟨⟨43/160, -31/160⟩, 3/320⟩
def center0700 : GaussianRat :=
  ⟨188321901/1000000000, -126012049/1000000000⟩
def contact0700 : RatBall := localContactBall tau0700 center0700
def work0700 : RoundedTauEval :=
  evalTau precision tau0700 contact0700 logTwoBall

theorem center_sq0700 : (center0700.re : ℝ)^2 +
    (center0700.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0700]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0700 : work0700.theta.ok = true ∧
    work0700.jac.invOK = true ∧ acceptsUnitSq work0700.out = true := by decide +kernel

def cell0700 : CellCertificate where
  tauBall := tau0700
  contactCenter := center0700
  contactBall := contact0700
  work := work0700
  center_sq := center_sq0700
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0700.1
  jac_ok := checks0700.2.1
  accepted := checks0700.2.2

def tau0701 : RatBall :=
  ⟨⟨41/160, -29/160⟩, 3/320⟩
def center0701 : GaussianRat :=
  ⟨89605161/500000000, -4741701/40000000⟩
def contact0701 : RatBall := localContactBall tau0701 center0701
def work0701 : RoundedTauEval :=
  evalTau precision tau0701 contact0701 logTwoBall

theorem center_sq0701 : (center0701.re : ℝ)^2 +
    (center0701.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0701]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0701 : work0701.theta.ok = true ∧
    work0701.jac.invOK = true ∧ acceptsUnitSq work0701.out = true := by decide +kernel

def cell0701 : CellCertificate where
  tauBall := tau0701
  contactCenter := center0701
  contactBall := contact0701
  work := work0701
  center_sq := center_sq0701
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0701.1
  jac_ok := checks0701.2.1
  accepted := checks0701.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087


