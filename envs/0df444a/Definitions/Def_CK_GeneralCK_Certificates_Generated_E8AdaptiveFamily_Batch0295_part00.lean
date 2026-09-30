-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0295_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0295_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:19:23.244152+00:00
-- url     : https://prove2.me/theorems/6f7ea7f0-15f2-4cfa-9d05-4ca4079912cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0295 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2360 : RatBall :=
  ⟨⟨57/320, 101/320⟩, 3/640⟩
def center2360 : GaussianRat :=
  ⟨135347471/1000000000, 43651451/200000000⟩
def contact2360 : RatBall := localContactBall tau2360 center2360
def work2360 : RoundedTauEval :=
  evalTau precision tau2360 contact2360 logTwoBall

theorem center_sq2360 : (center2360.re : ℝ)^2 +
    (center2360.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2360]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2360 : work2360.theta.ok = true ∧
    work2360.jac.invOK = true ∧ acceptsUnitSq work2360.out = true := by decide +kernel

def cell2360 : CellCertificate where
  tauBall := tau2360
  contactCenter := center2360
  contactBall := contact2360
  work := work2360
  center_sq := center_sq2360
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2360.1
  jac_ok := checks2360.2.1
  accepted := checks2360.2.2

def tau2361 : RatBall :=
  ⟨⟨59/320, 101/320⟩, 3/640⟩
def center2361 : GaussianRat :=
  ⟨27985801/200000000, 54418229/250000000⟩
def contact2361 : RatBall := localContactBall tau2361 center2361
def work2361 : RoundedTauEval :=
  evalTau precision tau2361 contact2361 logTwoBall

theorem center_sq2361 : (center2361.re : ℝ)^2 +
    (center2361.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2361]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2361 : work2361.theta.ok = true ∧
    work2361.jac.invOK = true ∧ acceptsUnitSq work2361.out = true := by decide +kernel

def cell2361 : CellCertificate where
  tauBall := tau2361
  contactCenter := center2361
  contactBall := contact2361
  work := work2361
  center_sq := center_sq2361
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2361.1
  jac_ok := checks2361.2.1
  accepted := checks2361.2.2

def tau2362 : RatBall :=
  ⟨⟨57/320, 103/320⟩, 3/640⟩
def center2362 : GaussianRat :=
  ⟨135931497/1000000000, 55713833/250000000⟩
def contact2362 : RatBall := localContactBall tau2362 center2362
def work2362 : RoundedTauEval :=
  evalTau precision tau2362 contact2362 logTwoBall

theorem center_sq2362 : (center2362.re : ℝ)^2 +
    (center2362.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2362]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2362 : work2362.theta.ok = true ∧
    work2362.jac.invOK = true ∧ acceptsUnitSq work2362.out = true := by decide +kernel

def cell2362 : CellCertificate where
  tauBall := tau2362
  contactCenter := center2362
  contactBall := contact2362
  work := work2362
  center_sq := center_sq2362
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2362.1
  jac_ok := checks2362.2.1
  accepted := checks2362.2.2

def tau2363 : RatBall :=
  ⟨⟨59/320, 103/320⟩, 3/640⟩
def center2363 : GaussianRat :=
  ⟨140529903/1000000000, 222254637/1000000000⟩
def contact2363 : RatBall := localContactBall tau2363 center2363
def work2363 : RoundedTauEval :=
  evalTau precision tau2363 contact2363 logTwoBall

theorem center_sq2363 : (center2363.re : ℝ)^2 +
    (center2363.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2363]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2363 : work2363.theta.ok = true ∧
    work2363.jac.invOK = true ∧ acceptsUnitSq work2363.out = true := by decide +kernel

def cell2363 : CellCertificate where
  tauBall := tau2363
  contactCenter := center2363
  contactBall := contact2363
  work := work2363
  center_sq := center_sq2363
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2363.1
  jac_ok := checks2363.2.1
  accepted := checks2363.2.2

def tau2364 : RatBall :=
  ⟨⟨61/320, 101/320⟩, 3/640⟩
def center2364 : GaussianRat :=
  ⟨7224707/50000000, 217072079/1000000000⟩
def contact2364 : RatBall := localContactBall tau2364 center2364
def work2364 : RoundedTauEval :=
  evalTau precision tau2364 contact2364 logTwoBall

theorem center_sq2364 : (center2364.re : ℝ)^2 +
    (center2364.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2364]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2364 : work2364.theta.ok = true ∧
    work2364.jac.invOK = true ∧ acceptsUnitSq work2364.out = true := by decide +kernel

def cell2364 : CellCertificate where
  tauBall := tau2364
  contactCenter := center2364
  contactBall := contact2364
  work := work2364
  center_sq := center_sq2364
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2364.1
  jac_ok := checks2364.2.1
  accepted := checks2364.2.2

def tau2365 : RatBall :=
  ⟨⟨63/320, 101/320⟩, 3/640⟩
def center2365 : GaussianRat :=
  ⟨74521233/500000000, 108227539/500000000⟩
def contact2365 : RatBall := localContactBall tau2365 center2365
def work2365 : RoundedTauEval :=
  evalTau precision tau2365 contact2365 logTwoBall

theorem center_sq2365 : (center2365.re : ℝ)^2 +
    (center2365.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2365]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2365 : work2365.theta.ok = true ∧
    work2365.jac.invOK = true ∧ acceptsUnitSq work2365.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295


