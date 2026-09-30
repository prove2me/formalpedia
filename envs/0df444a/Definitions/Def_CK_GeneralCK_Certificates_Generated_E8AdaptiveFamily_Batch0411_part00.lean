-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0411_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0411_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:37:20.865211+00:00
-- url     : https://prove2.me/theorems/c8f5e2bf-2cf1-4f2e-8530-9ff002713c45
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0411 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3288 : RatBall :=
  ⟨⟨-93/640, 237/640⟩, 3/1280⟩
def center3288 : GaussianRat :=
  ⟨-115826349/1000000000, 52528557/200000000⟩
def contact3288 : RatBall := localContactBall tau3288 center3288
def work3288 : RoundedTauEval :=
  evalTau precision tau3288 contact3288 logTwoBall

theorem center_sq3288 : (center3288.re : ℝ)^2 +
    (center3288.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3288]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3288 : work3288.theta.ok = true ∧
    work3288.jac.invOK = true ∧ acceptsUnitSq work3288.out = true := by decide +kernel

def cell3288 : CellCertificate where
  tauBall := tau3288
  contactCenter := center3288
  contactBall := contact3288
  work := work3288
  center_sq := center_sq3288
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3288.1
  jac_ok := checks3288.2.1
  accepted := checks3288.2.2

def tau3289 : RatBall :=
  ⟨⟨-19/128, 239/640⟩, 3/1280⟩
def center3289 : GaussianRat :=
  ⟨-118563451/1000000000, 66188883/250000000⟩
def contact3289 : RatBall := localContactBall tau3289 center3289
def work3289 : RoundedTauEval :=
  evalTau precision tau3289 contact3289 logTwoBall

theorem center_sq3289 : (center3289.re : ℝ)^2 +
    (center3289.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3289]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3289 : work3289.theta.ok = true ∧
    work3289.jac.invOK = true ∧ acceptsUnitSq work3289.out = true := by decide +kernel

def cell3289 : CellCertificate where
  tauBall := tau3289
  contactCenter := center3289
  contactBall := contact3289
  work := work3289
  center_sq := center_sq3289
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3289.1
  jac_ok := checks3289.2.1
  accepted := checks3289.2.2

def tau3290 : RatBall :=
  ⟨⟨-93/640, 239/640⟩, 3/1280⟩
def center3290 : GaussianRat :=
  ⟨-116135629/1000000000, 265069807/1000000000⟩
def contact3290 : RatBall := localContactBall tau3290 center3290
def work3290 : RoundedTauEval :=
  evalTau precision tau3290 contact3290 logTwoBall

theorem center_sq3290 : (center3290.re : ℝ)^2 +
    (center3290.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3290]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3290 : work3290.theta.ok = true ∧
    work3290.jac.invOK = true ∧ acceptsUnitSq work3290.out = true := by decide +kernel

def cell3290 : CellCertificate where
  tauBall := tau3290
  contactCenter := center3290
  contactBall := contact3290
  work := work3290
  center_sq := center_sq3290
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3290.1
  jac_ok := checks3290.2.1
  accepted := checks3290.2.2

def tau3291 : RatBall :=
  ⟨⟨-91/640, 237/640⟩, 3/1280⟩
def center3291 : GaussianRat :=
  ⟨-22680033/200000000, 131473549/500000000⟩
def contact3291 : RatBall := localContactBall tau3291 center3291
def work3291 : RoundedTauEval :=
  evalTau precision tau3291 contact3291 logTwoBall

theorem center_sq3291 : (center3291.re : ℝ)^2 +
    (center3291.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3291]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3291 : work3291.theta.ok = true ∧
    work3291.jac.invOK = true ∧ acceptsUnitSq work3291.out = true := by decide +kernel

def cell3291 : CellCertificate where
  tauBall := tau3291
  contactCenter := center3291
  contactBall := contact3291
  work := work3291
  center_sq := center_sq3291
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3291.1
  jac_ok := checks3291.2.1
  accepted := checks3291.2.2

def tau3292 : RatBall :=
  ⟨⟨-89/640, 237/640⟩, 3/1280⟩
def center3292 : GaussianRat :=
  ⟨-55484957/500000000, 65811399/250000000⟩
def contact3292 : RatBall := localContactBall tau3292 center3292
def work3292 : RoundedTauEval :=
  evalTau precision tau3292 contact3292 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411


