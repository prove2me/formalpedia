-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0060_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0060_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:23:28.689196+00:00
-- url     : https://prove2.me/theorems/544a0d71-6a99-485c-97c1-3aaaf4b7905b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0060 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0060_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0482 : work0482.theta.ok = true ∧
    work0482.jac.invOK = true ∧ acceptsUnitSq work0482.out = true := by decide +kernel

def cell0482 : CellCertificate where
  tauBall := tau0482
  contactCenter := center0482
  contactBall := contact0482
  work := work0482
  center_sq := center_sq0482
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0482.1
  jac_ok := checks0482.2.1
  accepted := checks0482.2.2

def tau0483 : RatBall :=
  ⟨⟨-57/160, -27/160⟩, 3/320⟩
def center0483 : GaussianRat :=
  ⟨-242691133/1000000000, -103792249/1000000000⟩
def contact0483 : RatBall := localContactBall tau0483 center0483
def work0483 : RoundedTauEval :=
  evalTau precision tau0483 contact0483 logTwoBall

theorem center_sq0483 : (center0483.re : ℝ)^2 +
    (center0483.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0483]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0483 : work0483.theta.ok = true ∧
    work0483.jac.invOK = true ∧ acceptsUnitSq work0483.out = true := by decide +kernel

def cell0483 : CellCertificate where
  tauBall := tau0483
  contactCenter := center0483
  contactBall := contact0483
  work := work0483
  center_sq := center_sq0483
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0483.1
  jac_ok := checks0483.2.1
  accepted := checks0483.2.2

def tau0484 : RatBall :=
  ⟨⟨-59/160, -5/32⟩, 3/320⟩
def center0484 : GaussianRat :=
  ⟨-1996423/8000000, -19043899/200000000⟩
def contact0484 : RatBall := localContactBall tau0484 center0484
def work0484 : RoundedTauEval :=
  evalTau precision tau0484 contact0484 logTwoBall

theorem center_sq0484 : (center0484.re : ℝ)^2 +
    (center0484.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0484]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0484 : work0484.theta.ok = true ∧
    work0484.jac.invOK = true ∧ acceptsUnitSq work0484.out = true := by decide +kernel

def cell0484 : CellCertificate where
  tauBall := tau0484
  contactCenter := center0484
  contactBall := contact0484
  work := work0484
  center_sq := center_sq0484
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0484.1
  jac_ok := checks0484.2.1
  accepted := checks0484.2.2

def tau0485 : RatBall :=
  ⟨⟨-57/160, -5/32⟩, 3/320⟩
def center0485 : GaussianRat :=
  ⟨-7557593/31250000, -96039881/1000000000⟩
def contact0485 : RatBall := localContactBall tau0485 center0485

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060


