-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0059_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0059_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:24:40.962099+00:00
-- url     : https://prove2.me/theorems/cd766b4d-485a-4e8e-925b-e0a7607d2d90
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0059 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0059_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell0475 : CellCertificate where
  tauBall := tau0475
  contactCenter := center0475
  contactBall := contact0475
  work := work0475
  center_sq := center_sq0475
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0475.1
  jac_ok := checks0475.2.1
  accepted := checks0475.2.2

def tau0476 : RatBall :=
  ⟨⟨-13/160, -9/32⟩, 3/320⟩
def center0476 : GaussianRat :=
  ⟨-30576347/500000000, -99498463/500000000⟩
def contact0476 : RatBall := localContactBall tau0476 center0476
def work0476 : RoundedTauEval :=
  evalTau precision tau0476 contact0476 logTwoBall

theorem center_sq0476 : (center0476.re : ℝ)^2 +
    (center0476.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0476]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0476 : work0476.theta.ok = true ∧
    work0476.jac.invOK = true ∧ acceptsUnitSq work0476.out = true := by decide +kernel

def cell0476 : CellCertificate where
  tauBall := tau0476
  contactCenter := center0476
  contactBall := contact0476
  work := work0476
  center_sq := center_sq0476
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0476.1
  jac_ok := checks0476.2.1
  accepted := checks0476.2.2

def tau0477 : RatBall :=
  ⟨⟨-11/160, -47/160⟩, 3/320⟩
def center0477 : GaussianRat :=
  ⟨-13053307/250000000, -208849073/1000000000⟩
def contact0477 : RatBall := localContactBall tau0477 center0477
def work0477 : RoundedTauEval :=
  evalTau precision tau0477 contact0477 logTwoBall

theorem center_sq0477 : (center0477.re : ℝ)^2 +
    (center0477.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0477]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0477 : work0477.theta.ok = true ∧
    work0477.jac.invOK = true ∧ acceptsUnitSq work0477.out = true := by decide +kernel

def cell0477 : CellCertificate where
  tauBall := tau0477
  contactCenter := center0477
  contactBall := contact0477
  work := work0477
  center_sq := center_sq0477
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0477.1
  jac_ok := checks0477.2.1
  accepted := checks0477.2.2

def tau0478 : RatBall :=
  ⟨⟨-9/160, -47/160⟩, 3/320⟩
def center0478 : GaussianRat :=
  ⟨-42754839/1000000000, -41848559/200000000⟩
def contact0478 : RatBall := localContactBall tau0478 center0478
def work0478 : RoundedTauEval :=
  evalTau precision tau0478 contact0478 logTwoBall

theorem center_sq0478 : (center0478.re : ℝ)^2 +
    (center0478.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0478]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0478 : work0478.theta.ok = true ∧
    work0478.jac.invOK = true ∧ acceptsUnitSq work0478.out = true := by decide +kernel

def cell0478 : CellCertificate where
  tauBall := tau0478
  contactCenter := center0478
  contactBall := contact0478
  work := work0478
  center_sq := center_sq0478
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0478.1
  jac_ok := checks0478.2.1
  accepted := checks0478.2.2

def tau0479 : RatBall :=
  ⟨⟨-11/160, -9/32⟩, 3/320⟩
def center0479 : GaussianRat :=
  ⟨-25896777/500000000, -199440199/1000000000⟩
def contact0479 : RatBall := localContactBall tau0479 center0479
def work0479 : RoundedTauEval :=
  evalTau precision tau0479 contact0479 logTwoBall

theorem center_sq0479 : (center0479.re : ℝ)^2 +
    (center0479.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0479]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059


