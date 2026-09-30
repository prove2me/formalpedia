-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0092_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0092_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:48:30.245182+00:00
-- url     : https://prove2.me/theorems/f70873ae-6c26-4eb6-b92c-c160ed7b7b98
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0092 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0092_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0739 : RatBall :=
  ⟨⟨11/32, -21/160⟩, 3/320⟩
def center0739 : GaussianRat :=
  ⟨232602861/1000000000, -81248009/1000000000⟩
def contact0739 : RatBall := localContactBall tau0739 center0739
def work0739 : RoundedTauEval :=
  evalTau precision tau0739 contact0739 logTwoBall

theorem center_sq0739 : (center0739.re : ℝ)^2 +
    (center0739.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0739]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0739 : work0739.theta.ok = true ∧
    work0739.jac.invOK = true ∧ acceptsUnitSq work0739.out = true := by decide +kernel

def cell0739 : CellCertificate where
  tauBall := tau0739
  contactCenter := center0739
  contactBall := contact0739
  work := work0739
  center_sq := center_sq0739
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0739.1
  jac_ok := checks0739.2.1
  accepted := checks0739.2.2

def tau0740 : RatBall :=
  ⟨⟨53/160, -19/160⟩, 3/320⟩
def center0740 : GaussianRat :=
  ⟨56041997/250000000, -74061203/1000000000⟩
def contact0740 : RatBall := localContactBall tau0740 center0740
def work0740 : RoundedTauEval :=
  evalTau precision tau0740 contact0740 logTwoBall

theorem center_sq0740 : (center0740.re : ℝ)^2 +
    (center0740.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0740]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0740 : work0740.theta.ok = true ∧
    work0740.jac.invOK = true ∧ acceptsUnitSq work0740.out = true := by decide +kernel

def cell0740 : CellCertificate where
  tauBall := tau0740
  contactCenter := center0740
  contactBall := contact0740
  work := work0740
  center_sq := center_sq0740
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0740.1
  jac_ok := checks0740.2.1
  accepted := checks0740.2.2

def tau0741 : RatBall :=
  ⟨⟨11/32, -19/160⟩, 3/320⟩
def center0741 : GaussianRat :=
  ⟨231972447/1000000000, -73469819/1000000000⟩
def contact0741 : RatBall := localContactBall tau0741 center0741
def work0741 : RoundedTauEval :=
  evalTau precision tau0741 contact0741 logTwoBall

theorem center_sq0741 : (center0741.re : ℝ)^2 +
    (center0741.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0741]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0741 : work0741.theta.ok = true ∧
    work0741.jac.invOK = true ∧ acceptsUnitSq work0741.out = true := by decide +kernel

def cell0741 : CellCertificate where
  tauBall := tau0741
  contactCenter := center0741
  contactBall := contact0741
  work := work0741
  center_sq := center_sq0741
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0741.1
  jac_ok := checks0741.2.1
  accepted := checks0741.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092


