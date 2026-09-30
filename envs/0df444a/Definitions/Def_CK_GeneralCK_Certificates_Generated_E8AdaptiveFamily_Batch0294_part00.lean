-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0294_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0294_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:23:33.599722+00:00
-- url     : https://prove2.me/theorems/2dcec634-f0fa-4df4-adae-15ed1f2d058e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0294 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2352 : RatBall :=
  ⟨⟨57/320, 97/320⟩, 3/640⟩
def center2352 : GaussianRat :=
  ⟨67113521/500000000, 52277787/250000000⟩
def contact2352 : RatBall := localContactBall tau2352 center2352
def work2352 : RoundedTauEval :=
  evalTau precision tau2352 contact2352 logTwoBall

theorem center_sq2352 : (center2352.re : ℝ)^2 +
    (center2352.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2352]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2352 : work2352.theta.ok = true ∧
    work2352.jac.invOK = true ∧ acceptsUnitSq work2352.out = true := by decide +kernel

def cell2352 : CellCertificate where
  tauBall := tau2352
  contactCenter := center2352
  contactBall := contact2352
  work := work2352
  center_sq := center_sq2352
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2352.1
  jac_ok := checks2352.2.1
  accepted := checks2352.2.2

def tau2353 : RatBall :=
  ⟨⟨59/320, 97/320⟩, 3/640⟩
def center2353 : GaussianRat :=
  ⟨13877609/100000000, 208558553/1000000000⟩
def contact2353 : RatBall := localContactBall tau2353 center2353
def work2353 : RoundedTauEval :=
  evalTau precision tau2353 contact2353 logTwoBall

theorem center_sq2353 : (center2353.re : ℝ)^2 +
    (center2353.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2353]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2353 : work2353.theta.ok = true ∧
    work2353.jac.invOK = true ∧ acceptsUnitSq work2353.out = true := by decide +kernel

def cell2353 : CellCertificate where
  tauBall := tau2353
  contactCenter := center2353
  contactBall := contact2353
  work := work2353
  center_sq := center_sq2353
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2353.1
  jac_ok := checks2353.2.1
  accepted := checks2353.2.2

def tau2354 : RatBall :=
  ⟨⟨57/320, 99/320⟩, 3/640⟩
def center2354 : GaussianRat :=
  ⟨5391177/40000000, 106838001/500000000⟩
def contact2354 : RatBall := localContactBall tau2354 center2354
def work2354 : RoundedTauEval :=
  evalTau precision tau2354 contact2354 logTwoBall

theorem center_sq2354 : (center2354.re : ℝ)^2 +
    (center2354.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2354]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2354 : work2354.theta.ok = true ∧
    work2354.jac.invOK = true ∧ acceptsUnitSq work2354.out = true := by decide +kernel

def cell2354 : CellCertificate where
  tauBall := tau2354
  contactCenter := center2354
  contactBall := contact2354
  work := work2354
  center_sq := center_sq2354
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2354.1
  jac_ok := checks2354.2.1
  accepted := checks2354.2.2

def tau2355 : RatBall :=
  ⟨⟨59/320, 99/320⟩, 3/640⟩
def center2355 : GaussianRat :=
  ⟨34836127/250000000, 53276923/250000000⟩
def contact2355 : RatBall := localContactBall tau2355 center2355
def work2355 : RoundedTauEval :=
  evalTau precision tau2355 contact2355 logTwoBall

theorem center_sq2355 : (center2355.re : ℝ)^2 +
    (center2355.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2355]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2355 : work2355.theta.ok = true ∧
    work2355.jac.invOK = true ∧ acceptsUnitSq work2355.out = true := by decide +kernel

def cell2355 : CellCertificate where
  tauBall := tau2355
  contactCenter := center2355
  contactBall := contact2355
  work := work2355
  center_sq := center_sq2355
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2355.1
  jac_ok := checks2355.2.1
  accepted := checks2355.2.2

def tau2356 : RatBall :=
  ⟨⟨61/320, 97/320⟩, 3/640⟩
def center2356 : GaussianRat :=
  ⟨143309371/1000000000, 103995141/500000000⟩
def contact2356 : RatBall := localContactBall tau2356 center2356
def work2356 : RoundedTauEval :=
  evalTau precision tau2356 contact2356 logTwoBall

theorem center_sq2356 : (center2356.re : ℝ)^2 +
    (center2356.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2356]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2356 : work2356.theta.ok = true ∧
    work2356.jac.invOK = true ∧ acceptsUnitSq work2356.out = true := by decide +kernel

def cell2356 : CellCertificate where
  tauBall := tau2356
  contactCenter := center2356
  contactBall := contact2356
  work := work2356
  center_sq := center_sq2356
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2356.1
  jac_ok := checks2356.2.1
  accepted := checks2356.2.2

def tau2357 : RatBall :=
  ⟨⟨63/320, 97/320⟩, 3/640⟩
def center2357 : GaussianRat :=
  ⟨147826489/1000000000, 2592583/12500000⟩
def contact2357 : RatBall := localContactBall tau2357 center2357
def work2357 : RoundedTauEval :=
  evalTau precision tau2357 contact2357 logTwoBall

theorem center_sq2357 : (center2357.re : ℝ)^2 +
    (center2357.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2357]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2357 : work2357.theta.ok = true ∧
    work2357.jac.invOK = true ∧ acceptsUnitSq work2357.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294


