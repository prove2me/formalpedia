-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0412
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0412
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:17:36.916505+00:00
-- url     : https://prove2.me/theorems/212e515c-64c8-4d28-9385-cf2b1f26d72d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0412` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0412` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0412` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0412 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0412.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0412 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0412

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3296 : RatBall :=
  ⟨⟨-17/128, 233/640⟩, 3/1280⟩
def center3296 : GaussianRat :=
  ⟨-105537631/1000000000, 258956581/1000000000⟩
def contact3296 : RatBall := localContactBall tau3296 center3296
def work3296 : RoundedTauEval :=
  evalTau precision tau3296 contact3296 logTwoBall

theorem center_sq3296 : (center3296.re : ℝ)^2 +
    (center3296.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3296]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3296 : work3296.theta.ok = true ∧
    work3296.jac.invOK = true ∧ acceptsUnitSq work3296.out = true := by decide +kernel

def cell3296 : CellCertificate where
  tauBall := tau3296
  contactCenter := center3296
  contactBall := contact3296
  work := work3296
  center_sq := center_sq3296
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3296.1
  jac_ok := checks3296.2.1
  accepted := checks3296.2.2

def tau3297 : RatBall :=
  ⟨⟨-87/640, 47/128⟩, 3/1280⟩
def center3297 : GaussianRat :=
  ⟨-21649587/200000000, 815953/3125000⟩
def contact3297 : RatBall := localContactBall tau3297 center3297
def work3297 : RoundedTauEval :=
  evalTau precision tau3297 contact3297 logTwoBall

theorem center_sq3297 : (center3297.re : ℝ)^2 +
    (center3297.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3297]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3297 : work3297.theta.ok = true ∧
    work3297.jac.invOK = true ∧ acceptsUnitSq work3297.out = true := by decide +kernel

def cell3297 : CellCertificate where
  tauBall := tau3297
  contactCenter := center3297
  contactBall := contact3297
  work := work3297
  center_sq := center_sq3297
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3297.1
  jac_ok := checks3297.2.1
  accepted := checks3297.2.2

def tau3298 : RatBall :=
  ⟨⟨-17/128, 47/128⟩, 3/1280⟩
def center3298 : GaussianRat :=
  ⟨-13226959/125000000, 130693913/500000000⟩
def contact3298 : RatBall := localContactBall tau3298 center3298
def work3298 : RoundedTauEval :=
  evalTau precision tau3298 contact3298 logTwoBall

theorem center_sq3298 : (center3298.re : ℝ)^2 +
    (center3298.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3298]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3298 : work3298.theta.ok = true ∧
    work3298.jac.invOK = true ∧ acceptsUnitSq work3298.out = true := by decide +kernel

def cell3298 : CellCertificate where
  tauBall := tau3298
  contactCenter := center3298
  contactBall := contact3298
  work := work3298
  center_sq := center_sq3298
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3298.1
  jac_ok := checks3298.2.1
  accepted := checks3298.2.2

def tau3299 : RatBall :=
  ⟨⟨-83/640, 233/640⟩, 3/1280⟩
def center3299 : GaussianRat :=
  ⟨-103107441/1000000000, 129614913/500000000⟩
def contact3299 : RatBall := localContactBall tau3299 center3299
def work3299 : RoundedTauEval :=
  evalTau precision tau3299 contact3299 logTwoBall

theorem center_sq3299 : (center3299.re : ℝ)^2 +
    (center3299.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3299]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3299 : work3299.theta.ok = true ∧
    work3299.jac.invOK = true ∧ acceptsUnitSq work3299.out = true := by decide +kernel

def cell3299 : CellCertificate where
  tauBall := tau3299
  contactCenter := center3299
  contactBall := contact3299
  work := work3299
  center_sq := center_sq3299
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3299.1
  jac_ok := checks3299.2.1
  accepted := checks3299.2.2

def tau3300 : RatBall :=
  ⟨⟨-81/640, 233/640⟩, 3/1280⟩
def center3300 : GaussianRat :=
  ⟨-12584197/125000000, 1013661/3906250⟩
def contact3300 : RatBall := localContactBall tau3300 center3300
def work3300 : RoundedTauEval :=
  evalTau precision tau3300 contact3300 logTwoBall

theorem center_sq3300 : (center3300.re : ℝ)^2 +
    (center3300.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3300]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3300 : work3300.theta.ok = true ∧
    work3300.jac.invOK = true ∧ acceptsUnitSq work3300.out = true := by decide +kernel

def cell3300 : CellCertificate where
  tauBall := tau3300
  contactCenter := center3300
  contactBall := contact3300
  work := work3300
  center_sq := center_sq3300
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3300.1
  jac_ok := checks3300.2.1
  accepted := checks3300.2.2

def tau3301 : RatBall :=
  ⟨⟨-83/640, 47/128⟩, 3/1280⟩
def center3301 : GaussianRat :=
  ⟨-25844903/250000000, 261664807/1000000000⟩
def contact3301 : RatBall := localContactBall tau3301 center3301
def work3301 : RoundedTauEval :=
  evalTau precision tau3301 contact3301 logTwoBall

theorem center_sq3301 : (center3301.re : ℝ)^2 +
    (center3301.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3301]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3301 : work3301.theta.ok = true ∧
    work3301.jac.invOK = true ∧ acceptsUnitSq work3301.out = true := by decide +kernel

def cell3301 : CellCertificate where
  tauBall := tau3301
  contactCenter := center3301
  contactBall := contact3301
  work := work3301
  center_sq := center_sq3301
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3301.1
  jac_ok := checks3301.2.1
  accepted := checks3301.2.2

def tau3302 : RatBall :=
  ⟨⟨-81/640, 47/128⟩, 3/1280⟩
def center3302 : GaussianRat :=
  ⟨-100939831/1000000000, 261935857/1000000000⟩
def contact3302 : RatBall := localContactBall tau3302 center3302
def work3302 : RoundedTauEval :=
  evalTau precision tau3302 contact3302 logTwoBall

theorem center_sq3302 : (center3302.re : ℝ)^2 +
    (center3302.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3302]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3302 : work3302.theta.ok = true ∧
    work3302.jac.invOK = true ∧ acceptsUnitSq work3302.out = true := by decide +kernel

def cell3302 : CellCertificate where
  tauBall := tau3302
  contactCenter := center3302
  contactBall := contact3302
  work := work3302
  center_sq := center_sq3302
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3302.1
  jac_ok := checks3302.2.1
  accepted := checks3302.2.2

def tau3303 : RatBall :=
  ⟨⟨-87/640, 237/640⟩, 3/1280⟩
def center3303 : GaussianRat :=
  ⟨-108535671/1000000000, 263538231/1000000000⟩
def contact3303 : RatBall := localContactBall tau3303 center3303
def work3303 : RoundedTauEval :=
  evalTau precision tau3303 contact3303 logTwoBall

theorem center_sq3303 : (center3303.re : ℝ)^2 +
    (center3303.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3303]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3303 : work3303.theta.ok = true ∧
    work3303.jac.invOK = true ∧ acceptsUnitSq work3303.out = true := by decide +kernel

def cell3303 : CellCertificate where
  tauBall := tau3303
  contactCenter := center3303
  contactBall := contact3303
  work := work3303
  center_sq := center_sq3303
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3303.1
  jac_ok := checks3303.2.1
  accepted := checks3303.2.2

def cells : List CellCertificate := [cell3296, cell3297, cell3298, cell3299, cell3300, cell3301, cell3302, cell3303]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0412

end


