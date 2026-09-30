-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0407
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0407
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:36:15.440366+00:00
-- url     : https://prove2.me/theorems/b8135dde-55fe-44e9-ac82-cf64f13cf1b6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0407` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0407` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0407` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0407 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0407.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0407 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0407

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3256 : RatBall :=
  ⟨⟨-103/640, 231/640⟩, 3/1280⟩
def center3256 : GaussianRat :=
  ⟨-63453799/500000000, 253852567/1000000000⟩
def contact3256 : RatBall := localContactBall tau3256 center3256
def work3256 : RoundedTauEval :=
  evalTau precision tau3256 contact3256 logTwoBall

theorem center_sq3256 : (center3256.re : ℝ)^2 +
    (center3256.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3256]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3256 : work3256.theta.ok = true ∧
    work3256.jac.invOK = true ∧ acceptsUnitSq work3256.out = true := by decide +kernel

def cell3256 : CellCertificate where
  tauBall := tau3256
  contactCenter := center3256
  contactBall := contact3256
  work := work3256
  center_sq := center_sq3256
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3256.1
  jac_ok := checks3256.2.1
  accepted := checks3256.2.2

def tau3257 : RatBall :=
  ⟨⟨-101/640, 231/640⟩, 3/1280⟩
def center3257 : GaussianRat :=
  ⟨-15564887/125000000, 254172071/1000000000⟩
def contact3257 : RatBall := localContactBall tau3257 center3257
def work3257 : RoundedTauEval :=
  evalTau precision tau3257 contact3257 logTwoBall

theorem center_sq3257 : (center3257.re : ℝ)^2 +
    (center3257.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3257]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3257 : work3257.theta.ok = true ∧
    work3257.jac.invOK = true ∧ acceptsUnitSq work3257.out = true := by decide +kernel

def cell3257 : CellCertificate where
  tauBall := tau3257
  contactCenter := center3257
  contactBall := contact3257
  work := work3257
  center_sq := center_sq3257
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3257.1
  jac_ok := checks3257.2.1
  accepted := checks3257.2.2

def tau3258 : RatBall :=
  ⟨⟨-99/640, 229/640⟩, 3/1280⟩
def center3258 : GaussianRat :=
  ⟨-30454243/250000000, 126047019/500000000⟩
def contact3258 : RatBall := localContactBall tau3258 center3258
def work3258 : RoundedTauEval :=
  evalTau precision tau3258 contact3258 logTwoBall

theorem center_sq3258 : (center3258.re : ℝ)^2 +
    (center3258.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3258]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3258 : work3258.theta.ok = true ∧
    work3258.jac.invOK = true ∧ acceptsUnitSq work3258.out = true := by decide +kernel

def cell3258 : CellCertificate where
  tauBall := tau3258
  contactCenter := center3258
  contactBall := contact3258
  work := work3258
  center_sq := center_sq3258
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3258.1
  jac_ok := checks3258.2.1
  accepted := checks3258.2.2

def tau3259 : RatBall :=
  ⟨⟨-97/640, 229/640⟩, 3/1280⟩
def center3259 : GaussianRat :=
  ⟨-119425411/1000000000, 252398639/1000000000⟩
def contact3259 : RatBall := localContactBall tau3259 center3259
def work3259 : RoundedTauEval :=
  evalTau precision tau3259 contact3259 logTwoBall

theorem center_sq3259 : (center3259.re : ℝ)^2 +
    (center3259.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3259]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3259 : work3259.theta.ok = true ∧
    work3259.jac.invOK = true ∧ acceptsUnitSq work3259.out = true := by decide +kernel

def cell3259 : CellCertificate where
  tauBall := tau3259
  contactCenter := center3259
  contactBall := contact3259
  work := work3259
  center_sq := center_sq3259
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3259.1
  jac_ok := checks3259.2.1
  accepted := checks3259.2.2

def tau3260 : RatBall :=
  ⟨⟨-99/640, 231/640⟩, 3/1280⟩
def center3260 : GaussianRat :=
  ⟨-122126333/1000000000, 127243109/500000000⟩
def contact3260 : RatBall := localContactBall tau3260 center3260
def work3260 : RoundedTauEval :=
  evalTau precision tau3260 contact3260 logTwoBall

theorem center_sq3260 : (center3260.re : ℝ)^2 +
    (center3260.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3260]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3260 : work3260.theta.ok = true ∧
    work3260.jac.invOK = true ∧ acceptsUnitSq work3260.out = true := by decide +kernel

def cell3260 : CellCertificate where
  tauBall := tau3260
  contactCenter := center3260
  contactBall := contact3260
  work := work3260
  center_sq := center_sq3260
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3260.1
  jac_ok := checks3260.2.1
  accepted := checks3260.2.2

def tau3261 : RatBall :=
  ⟨⟨-97/640, 231/640⟩, 3/1280⟩
def center3261 : GaussianRat :=
  ⟨-59864687/500000000, 254794957/1000000000⟩
def contact3261 : RatBall := localContactBall tau3261 center3261
def work3261 : RoundedTauEval :=
  evalTau precision tau3261 contact3261 logTwoBall

theorem center_sq3261 : (center3261.re : ℝ)^2 +
    (center3261.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3261]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3261 : work3261.theta.ok = true ∧
    work3261.jac.invOK = true ∧ acceptsUnitSq work3261.out = true := by decide +kernel

def cell3261 : CellCertificate where
  tauBall := tau3261
  contactCenter := center3261
  contactBall := contact3261
  work := work3261
  center_sq := center_sq3261
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3261.1
  jac_ok := checks3261.2.1
  accepted := checks3261.2.2

def tau3262 : RatBall :=
  ⟨⟨-109/640, 233/640⟩, 3/1280⟩
def center3262 : GaussianRat :=
  ⟨-134387007/1000000000, 127619041/500000000⟩
def contact3262 : RatBall := localContactBall tau3262 center3262
def work3262 : RoundedTauEval :=
  evalTau precision tau3262 contact3262 logTwoBall

theorem center_sq3262 : (center3262.re : ℝ)^2 +
    (center3262.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3262]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3262 : work3262.theta.ok = true ∧
    work3262.jac.invOK = true ∧ acceptsUnitSq work3262.out = true := by decide +kernel

def cell3262 : CellCertificate where
  tauBall := tau3262
  contactCenter := center3262
  contactBall := contact3262
  work := work3262
  center_sq := center_sq3262
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3262.1
  jac_ok := checks3262.2.1
  accepted := checks3262.2.2

def tau3263 : RatBall :=
  ⟨⟨-107/640, 233/640⟩, 3/1280⟩
def center3263 : GaussianRat :=
  ⟨-132006469/1000000000, 255577867/1000000000⟩
def contact3263 : RatBall := localContactBall tau3263 center3263
def work3263 : RoundedTauEval :=
  evalTau precision tau3263 contact3263 logTwoBall

theorem center_sq3263 : (center3263.re : ℝ)^2 +
    (center3263.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3263]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3263 : work3263.theta.ok = true ∧
    work3263.jac.invOK = true ∧ acceptsUnitSq work3263.out = true := by decide +kernel

def cell3263 : CellCertificate where
  tauBall := tau3263
  contactCenter := center3263
  contactBall := contact3263
  work := work3263
  center_sq := center_sq3263
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3263.1
  jac_ok := checks3263.2.1
  accepted := checks3263.2.2

def cells : List CellCertificate := [cell3256, cell3257, cell3258, cell3259, cell3260, cell3261, cell3262, cell3263]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0407

end


