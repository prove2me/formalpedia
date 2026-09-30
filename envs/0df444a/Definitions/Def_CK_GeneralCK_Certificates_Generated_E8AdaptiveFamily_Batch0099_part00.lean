-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0099_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0099_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:11:51.670497+00:00
-- url     : https://prove2.me/theorems/c70188f4-20f2-449b-b753-60e20d379c0c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0099 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0792 : RatBall :=
  ⟨⟨-59/160, 19/160⟩, 3/320⟩
def center0792 : GaussianRat :=
  ⟨-247383851/1000000000, 72251673/1000000000⟩
def contact0792 : RatBall := localContactBall tau0792 center0792
def work0792 : RoundedTauEval :=
  evalTau precision tau0792 contact0792 logTwoBall

theorem center_sq0792 : (center0792.re : ℝ)^2 +
    (center0792.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0792]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0792 : work0792.theta.ok = true ∧
    work0792.jac.invOK = true ∧ acceptsUnitSq work0792.out = true := by decide +kernel

def cell0792 : CellCertificate where
  tauBall := tau0792
  contactCenter := center0792
  contactBall := contact0792
  work := work0792
  center_sq := center_sq0792
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0792.1
  jac_ok := checks0792.2.1
  accepted := checks0792.2.2

def tau0793 : RatBall :=
  ⟨⟨-57/160, 19/160⟩, 3/320⟩
def center0793 : GaussianRat :=
  ⟨-239711471/1000000000, 72866371/1000000000⟩
def contact0793 : RatBall := localContactBall tau0793 center0793
def work0793 : RoundedTauEval :=
  evalTau precision tau0793 contact0793 logTwoBall

theorem center_sq0793 : (center0793.re : ℝ)^2 +
    (center0793.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0793]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0793 : work0793.theta.ok = true ∧
    work0793.jac.invOK = true ∧ acceptsUnitSq work0793.out = true := by decide +kernel

def cell0793 : CellCertificate where
  tauBall := tau0793
  contactCenter := center0793
  contactBall := contact0793
  work := work0793
  center_sq := center_sq0793
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0793.1
  jac_ok := checks0793.2.1
  accepted := checks0793.2.2

def tau0794 : RatBall :=
  ⟨⟨-61/160, 21/160⟩, 3/320⟩
def center0794 : GaussianRat :=
  ⟨-15978319/62500000, 79201909/1000000000⟩
def contact0794 : RatBall := localContactBall tau0794 center0794
def work0794 : RoundedTauEval :=
  evalTau precision tau0794 contact0794 logTwoBall

theorem center_sq0794 : (center0794.re : ℝ)^2 +
    (center0794.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0794]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0794 : work0794.theta.ok = true ∧
    work0794.jac.invOK = true ∧ acceptsUnitSq work0794.out = true := by decide +kernel

def cell0794 : CellCertificate where
  tauBall := tau0794
  contactCenter := center0794
  contactBall := contact0794
  work := work0794
  center_sq := center_sq0794
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0794.1
  jac_ok := checks0794.2.1
  accepted := checks0794.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099


