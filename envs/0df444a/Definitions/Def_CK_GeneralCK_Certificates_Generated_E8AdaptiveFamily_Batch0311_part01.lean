-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0311_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0311_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:07:41.925697+00:00
-- url     : https://prove2.me/theorems/a48efec9-9233-45e5-9a03-bed2c1e97567
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0311 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0311_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell2491 : CellCertificate where
  tauBall := tau2491
  contactCenter := center2491
  contactBall := contact2491
  work := work2491
  center_sq := center_sq2491
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2491.1
  jac_ok := checks2491.2.1
  accepted := checks2491.2.2

def tau2492 : RatBall :=
  ⟨⟨93/320, 89/320⟩, 3/640⟩
def center2492 : GaussianRat :=
  ⟨84181/400000, 180208911/1000000000⟩
def contact2492 : RatBall := localContactBall tau2492 center2492
def work2492 : RoundedTauEval :=
  evalTau precision tau2492 contact2492 logTwoBall

theorem center_sq2492 : (center2492.re : ℝ)^2 +
    (center2492.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2492]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2492 : work2492.theta.ok = true ∧
    work2492.jac.invOK = true ∧ acceptsUnitSq work2492.out = true := by decide +kernel

def cell2492 : CellCertificate where
  tauBall := tau2492
  contactCenter := center2492
  contactBall := contact2492
  work := work2492
  center_sq := center_sq2492
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2492.1
  jac_ok := checks2492.2.1
  accepted := checks2492.2.2

def tau2493 : RatBall :=
  ⟨⟨89/320, 93/320⟩, 3/640⟩
def center2493 : GaussianRat :=
  ⟨50860061/250000000, 2969643/15625000⟩
def contact2493 : RatBall := localContactBall tau2493 center2493
def work2493 : RoundedTauEval :=
  evalTau precision tau2493 contact2493 logTwoBall

theorem center_sq2493 : (center2493.re : ℝ)^2 +
    (center2493.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2493]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2493 : work2493.theta.ok = true ∧
    work2493.jac.invOK = true ∧ acceptsUnitSq work2493.out = true := by decide +kernel

def cell2493 : CellCertificate where
  tauBall := tau2493
  contactCenter := center2493
  contactBall := contact2493
  work := work2493
  center_sq := center_sq2493
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2493.1
  jac_ok := checks2493.2.1
  accepted := checks2493.2.2

def tau2494 : RatBall :=
  ⟨⟨109/320, 13/64⟩, 3/640⟩
def center2494 : GaussianRat :=
  ⟨29446781/125000000, 63266993/500000000⟩
def contact2494 : RatBall := localContactBall tau2494 center2494
def work2494 : RoundedTauEval :=
  evalTau precision tau2494 contact2494 logTwoBall

theorem center_sq2494 : (center2494.re : ℝ)^2 +
    (center2494.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2494]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2494 : work2494.theta.ok = true ∧
    work2494.jac.invOK = true ∧ acceptsUnitSq work2494.out = true := by decide +kernel

def cell2494 : CellCertificate where
  tauBall := tau2494
  contactCenter := center2494
  contactBall := contact2494
  work := work2494
  center_sq := center_sq2494
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2494.1
  jac_ok := checks2494.2.1
  accepted := checks2494.2.2

def tau2495 : RatBall :=
  ⟨⟨111/320, 13/64⟩, 3/640⟩
def center2495 : GaussianRat :=
  ⟨239515009/1000000000, 31500643/250000000⟩
def contact2495 : RatBall := localContactBall tau2495 center2495
def work2495 : RoundedTauEval :=
  evalTau precision tau2495 contact2495 logTwoBall

theorem center_sq2495 : (center2495.re : ℝ)^2 +
    (center2495.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2495]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311


