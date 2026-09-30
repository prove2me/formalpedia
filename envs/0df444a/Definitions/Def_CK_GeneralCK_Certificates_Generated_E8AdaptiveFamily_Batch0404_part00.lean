-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0404_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0404_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:22:08.975+00:00
-- url     : https://prove2.me/theorems/9f2ffbca-0552-4af4-95f2-fc555e0996b1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0404 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3232 : RatBall :=
  ⟨⟨-119/640, 227/640⟩, 3/1280⟩
def center3232 : GaussianRat :=
  ⟨-145138173/1000000000, 123210011/500000000⟩
def contact3232 : RatBall := localContactBall tau3232 center3232
def work3232 : RoundedTauEval :=
  evalTau precision tau3232 contact3232 logTwoBall

theorem center_sq3232 : (center3232.re : ℝ)^2 +
    (center3232.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3232]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3232 : work3232.theta.ok = true ∧
    work3232.jac.invOK = true ∧ acceptsUnitSq work3232.out = true := by decide +kernel

def cell3232 : CellCertificate where
  tauBall := tau3232
  contactCenter := center3232
  contactBall := contact3232
  work := work3232
  center_sq := center_sq3232
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3232.1
  jac_ok := checks3232.2.1
  accepted := checks3232.2.2

def tau3233 : RatBall :=
  ⟨⟨-117/640, 227/640⟩, 3/1280⟩
def center3233 : GaussianRat :=
  ⟨-142795751/1000000000, 246771071/1000000000⟩
def contact3233 : RatBall := localContactBall tau3233 center3233
def work3233 : RoundedTauEval :=
  evalTau precision tau3233 contact3233 logTwoBall

theorem center_sq3233 : (center3233.re : ℝ)^2 +
    (center3233.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3233]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3233 : work3233.theta.ok = true ∧
    work3233.jac.invOK = true ∧ acceptsUnitSq work3233.out = true := by decide +kernel

def cell3233 : CellCertificate where
  tauBall := tau3233
  contactCenter := center3233
  contactBall := contact3233
  work := work3233
  center_sq := center_sq3233
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3233.1
  jac_ok := checks3233.2.1
  accepted := checks3233.2.2

def tau3234 : RatBall :=
  ⟨⟨-23/128, 45/128⟩, 3/1280⟩
def center3234 : GaussianRat :=
  ⟨-5604287/40000000, 122385171/500000000⟩
def contact3234 : RatBall := localContactBall tau3234 center3234
def work3234 : RoundedTauEval :=
  evalTau precision tau3234 contact3234 logTwoBall

theorem center_sq3234 : (center3234.re : ℝ)^2 +
    (center3234.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3234]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3234 : work3234.theta.ok = true ∧
    work3234.jac.invOK = true ∧ acceptsUnitSq work3234.out = true := by decide +kernel

def cell3234 : CellCertificate where
  tauBall := tau3234
  contactCenter := center3234
  contactBall := contact3234
  work := work3234
  center_sq := center_sq3234
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3234.1
  jac_ok := checks3234.2.1
  accepted := checks3234.2.2

def tau3235 : RatBall :=
  ⟨⟨-113/640, 45/128⟩, 3/1280⟩
def center3235 : GaussianRat :=
  ⟨-137760383/1000000000, 245107147/1000000000⟩
def contact3235 : RatBall := localContactBall tau3235 center3235
def work3235 : RoundedTauEval :=
  evalTau precision tau3235 contact3235 logTwoBall

theorem center_sq3235 : (center3235.re : ℝ)^2 +
    (center3235.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3235]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3235 : work3235.theta.ok = true ∧
    work3235.jac.invOK = true ∧ acceptsUnitSq work3235.out = true := by decide +kernel

def cell3235 : CellCertificate where
  tauBall := tau3235
  contactCenter := center3235
  contactBall := contact3235
  work := work3235
  center_sq := center_sq3235
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3235.1
  jac_ok := checks3235.2.1
  accepted := checks3235.2.2

def tau3236 : RatBall :=
  ⟨⟨-23/128, 227/640⟩, 3/1280⟩
def center3236 : GaussianRat :=
  ⟨-140448677/1000000000, 247117293/1000000000⟩
def contact3236 : RatBall := localContactBall tau3236 center3236
def work3236 : RoundedTauEval :=
  evalTau precision tau3236 contact3236 logTwoBall

theorem center_sq3236 : (center3236.re : ℝ)^2 +
    (center3236.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3236]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3236 : work3236.theta.ok = true ∧
    work3236.jac.invOK = true ∧ acceptsUnitSq work3236.out = true := by decide +kernel

def cell3236 : CellCertificate where
  tauBall := tau3236
  contactCenter := center3236
  contactBall := contact3236
  work := work3236
  center_sq := center_sq3236
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3236.1
  jac_ok := checks3236.2.1
  accepted := checks3236.2.2

def tau3237 : RatBall :=
  ⟨⟨-113/640, 227/640⟩, 3/1280⟩
def center3237 : GaussianRat :=
  ⟨-138097011/1000000000, 61864659/250000000⟩
def contact3237 : RatBall := localContactBall tau3237 center3237
def work3237 : RoundedTauEval :=
  evalTau precision tau3237 contact3237 logTwoBall

theorem center_sq3237 : (center3237.re : ℝ)^2 +
    (center3237.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3237]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3237 : work3237.theta.ok = true ∧
    work3237.jac.invOK = true ∧ acceptsUnitSq work3237.out = true := by decide +kernel

def cell3237 : CellCertificate where
  tauBall := tau3237
  contactCenter := center3237
  contactBall := contact3237
  work := work3237
  center_sq := center_sq3237
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3237.1
  jac_ok := checks3237.2.1
  accepted := checks3237.2.2

def tau3238 : RatBall :=
  ⟨⟨-117/640, 229/640⟩, 3/1280⟩
def center3238 : GaussianRat :=
  ⟨-143146729/1000000000, 249118251/1000000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404


