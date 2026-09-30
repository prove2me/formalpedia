-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0409_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0409_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:08:08.400253+00:00
-- url     : https://prove2.me/theorems/59490784-ad93-418b-af68-1cf444f07676
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0409 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3272 : RatBall :=
  ⟨⟨-97/640, 47/128⟩, 3/1280⟩
def center3272 : GaussianRat :=
  ⟨-15043717/125000000, 259604029/1000000000⟩
def contact3272 : RatBall := localContactBall tau3272 center3272
def work3272 : RoundedTauEval :=
  evalTau precision tau3272 contact3272 logTwoBall

theorem center_sq3272 : (center3272.re : ℝ)^2 +
    (center3272.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3272]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3272 : work3272.theta.ok = true ∧
    work3272.jac.invOK = true ∧ acceptsUnitSq work3272.out = true := by decide +kernel

def cell3272 : CellCertificate where
  tauBall := tau3272
  contactCenter := center3272
  contactBall := contact3272
  work := work3272
  center_sq := center_sq3272
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3272.1
  jac_ok := checks3272.2.1
  accepted := checks3272.2.2

def tau3273 : RatBall :=
  ⟨⟨-99/640, 237/640⟩, 3/1280⟩
def center3273 : GaussianRat :=
  ⟨-123079793/1000000000, 65423867/250000000⟩
def contact3273 : RatBall := localContactBall tau3273 center3273
def work3273 : RoundedTauEval :=
  evalTau precision tau3273 contact3273 logTwoBall

theorem center_sq3273 : (center3273.re : ℝ)^2 +
    (center3273.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3273]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3273 : work3273.theta.ok = true ∧
    work3273.jac.invOK = true ∧ acceptsUnitSq work3273.out = true := by decide +kernel

def cell3273 : CellCertificate where
  tauBall := tau3273
  contactCenter := center3273
  contactBall := contact3273
  work := work3273
  center_sq := center_sq3273
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3273.1
  jac_ok := checks3273.2.1
  accepted := checks3273.2.2

def tau3274 : RatBall :=
  ⟨⟨-97/640, 237/640⟩, 3/1280⟩
def center3274 : GaussianRat :=
  ⟨-60333117/500000000, 6550423/25000000⟩
def contact3274 : RatBall := localContactBall tau3274 center3274
def work3274 : RoundedTauEval :=
  evalTau precision tau3274 contact3274 logTwoBall

theorem center_sq3274 : (center3274.re : ℝ)^2 +
    (center3274.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3274]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3274 : work3274.theta.ok = true ∧
    work3274.jac.invOK = true ∧ acceptsUnitSq work3274.out = true := by decide +kernel

def cell3274 : CellCertificate where
  tauBall := tau3274
  contactCenter := center3274
  contactBall := contact3274
  work := work3274
  center_sq := center_sq3274
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3274.1
  jac_ok := checks3274.2.1
  accepted := checks3274.2.2

def tau3275 : RatBall :=
  ⟨⟨-19/128, 229/640⟩, 3/1280⟩
def center3275 : GaussianRat :=
  ⟨-117029769/1000000000, 63174463/250000000⟩
def contact3275 : RatBall := localContactBall tau3275 center3275
def work3275 : RoundedTauEval :=
  evalTau precision tau3275 contact3275 logTwoBall

theorem center_sq3275 : (center3275.re : ℝ)^2 +
    (center3275.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3275]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3275 : work3275.theta.ok = true ∧
    work3275.jac.invOK = true ∧ acceptsUnitSq work3275.out = true := by decide +kernel

def cell3275 : CellCertificate where
  tauBall := tau3275
  contactCenter := center3275
  contactBall := contact3275
  work := work3275
  center_sq := center_sq3275
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3275.1
  jac_ok := checks3275.2.1
  accepted := checks3275.2.2

def tau3276 : RatBall :=
  ⟨⟨-93/640, 229/640⟩, 3/1280⟩
def center3276 : GaussianRat :=
  ⟨-28657529/250000000, 252991629/1000000000⟩
def contact3276 : RatBall := localContactBall tau3276 center3276
def work3276 : RoundedTauEval :=
  evalTau precision tau3276 contact3276 logTwoBall

theorem center_sq3276 : (center3276.re : ℝ)^2 +
    (center3276.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3276]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3276 : work3276.theta.ok = true ∧
    work3276.jac.invOK = true ∧ acceptsUnitSq work3276.out = true := by decide +kernel

def cell3276 : CellCertificate where
  tauBall := tau3276
  contactCenter := center3276
  contactBall := contact3276
  work := work3276
  center_sq := center_sq3276
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3276.1
  jac_ok := checks3276.2.1
  accepted := checks3276.2.2

def tau3277 : RatBall :=
  ⟨⟨-19/128, 231/640⟩, 3/1280⟩
def center3277 : GaussianRat :=
  ⟨-117328287/1000000000, 255098241/1000000000⟩
def contact3277 : RatBall := localContactBall tau3277 center3277
def work3277 : RoundedTauEval :=
  evalTau precision tau3277 contact3277 logTwoBall

theorem center_sq3277 : (center3277.re : ℝ)^2 +
    (center3277.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3277]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3277 : work3277.theta.ok = true ∧
    work3277.jac.invOK = true ∧ acceptsUnitSq work3277.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409


