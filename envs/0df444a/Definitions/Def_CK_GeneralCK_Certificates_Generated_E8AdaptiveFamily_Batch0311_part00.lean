-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0311_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0311_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:08:14.559176+00:00
-- url     : https://prove2.me/theorems/94896c33-5874-4102-bdd7-96d57784e493
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0311 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2488 : RatBall :=
  ⟨⟨89/320, 89/320⟩, 3/640⟩
def center2488 : GaussianRat :=
  ⟨40408359/200000000, 181587727/1000000000⟩
def contact2488 : RatBall := localContactBall tau2488 center2488
def work2488 : RoundedTauEval :=
  evalTau precision tau2488 contact2488 logTwoBall

theorem center_sq2488 : (center2488.re : ℝ)^2 +
    (center2488.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2488]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2488 : work2488.theta.ok = true ∧
    work2488.jac.invOK = true ∧ acceptsUnitSq work2488.out = true := by decide +kernel

def cell2488 : CellCertificate where
  tauBall := tau2488
  contactCenter := center2488
  contactBall := contact2488
  work := work2488
  center_sq := center_sq2488
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2488.1
  jac_ok := checks2488.2.1
  accepted := checks2488.2.2

def tau2489 : RatBall :=
  ⟨⟨91/320, 89/320⟩, 3/640⟩
def center2489 : GaussianRat :=
  ⟨103128439/500000000, 180903081/1000000000⟩
def contact2489 : RatBall := localContactBall tau2489 center2489
def work2489 : RoundedTauEval :=
  evalTau precision tau2489 contact2489 logTwoBall

theorem center_sq2489 : (center2489.re : ℝ)^2 +
    (center2489.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2489]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2489 : work2489.theta.ok = true ∧
    work2489.jac.invOK = true ∧ acceptsUnitSq work2489.out = true := by decide +kernel

def cell2489 : CellCertificate where
  tauBall := tau2489
  contactCenter := center2489
  contactBall := contact2489
  work := work2489
  center_sq := center_sq2489
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2489.1
  jac_ok := checks2489.2.1
  accepted := checks2489.2.2

def tau2490 : RatBall :=
  ⟨⟨89/320, 91/320⟩, 3/640⟩
def center2490 : GaussianRat :=
  ⟨202731249/1000000000, 37163483/200000000⟩
def contact2490 : RatBall := localContactBall tau2490 center2490
def work2490 : RoundedTauEval :=
  evalTau precision tau2490 contact2490 logTwoBall

theorem center_sq2490 : (center2490.re : ℝ)^2 +
    (center2490.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2490]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2490 : work2490.theta.ok = true ∧
    work2490.jac.invOK = true ∧ acceptsUnitSq work2490.out = true := by decide +kernel

def cell2490 : CellCertificate where
  tauBall := tau2490
  contactCenter := center2490
  contactBall := contact2490
  work := work2490
  center_sq := center_sq2490
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2490.1
  jac_ok := checks2490.2.1
  accepted := checks2490.2.2

def tau2491 : RatBall :=
  ⟨⟨91/320, 91/320⟩, 3/640⟩
def center2491 : GaussianRat :=
  ⟨51739029/250000000, 46278317/250000000⟩
def contact2491 : RatBall := localContactBall tau2491 center2491
def work2491 : RoundedTauEval :=
  evalTau precision tau2491 contact2491 logTwoBall

theorem center_sq2491 : (center2491.re : ℝ)^2 +
    (center2491.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2491]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2491 : work2491.theta.ok = true ∧
    work2491.jac.invOK = true ∧ acceptsUnitSq work2491.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311


