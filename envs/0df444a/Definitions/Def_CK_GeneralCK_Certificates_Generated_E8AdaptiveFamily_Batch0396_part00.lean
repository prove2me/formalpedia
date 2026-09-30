-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0396_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0396_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:21:38.621649+00:00
-- url     : https://prove2.me/theorems/72eb05ef-1b18-4576-9cec-c8cf172f65a3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0396 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3168 : RatBall :=
  ⟨⟨23/128, -229/640⟩, 3/1280⟩
def center3168 : GaussianRat :=
  ⟨70397387/500000000, -249469121/1000000000⟩
def contact3168 : RatBall := localContactBall tau3168 center3168
def work3168 : RoundedTauEval :=
  evalTau precision tau3168 contact3168 logTwoBall

theorem center_sq3168 : (center3168.re : ℝ)^2 +
    (center3168.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3168]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3168 : work3168.theta.ok = true ∧
    work3168.jac.invOK = true ∧ acceptsUnitSq work3168.out = true := by decide +kernel

def cell3168 : CellCertificate where
  tauBall := tau3168
  contactCenter := center3168
  contactBall := contact3168
  work := work3168
  center_sq := center_sq3168
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3168.1
  jac_ok := checks3168.2.1
  accepted := checks3168.2.2

def tau3169 : RatBall :=
  ⟨⟨117/640, -229/640⟩, 3/1280⟩
def center3169 : GaussianRat :=
  ⟨143146729/1000000000, -249118251/1000000000⟩
def contact3169 : RatBall := localContactBall tau3169 center3169
def work3169 : RoundedTauEval :=
  evalTau precision tau3169 contact3169 logTwoBall

theorem center_sq3169 : (center3169.re : ℝ)^2 +
    (center3169.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3169]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3169 : work3169.theta.ok = true ∧
    work3169.jac.invOK = true ∧ acceptsUnitSq work3169.out = true := by decide +kernel

def cell3169 : CellCertificate where
  tauBall := tau3169
  contactCenter := center3169
  contactBall := contact3169
  work := work3169
  center_sq := center_sq3169
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3169.1
  jac_ok := checks3169.2.1
  accepted := checks3169.2.2

def tau3170 : RatBall :=
  ⟨⟨113/640, -227/640⟩, 3/1280⟩
def center3170 : GaussianRat :=
  ⟨138097011/1000000000, -61864659/250000000⟩
def contact3170 : RatBall := localContactBall tau3170 center3170
def work3170 : RoundedTauEval :=
  evalTau precision tau3170 contact3170 logTwoBall

theorem center_sq3170 : (center3170.re : ℝ)^2 +
    (center3170.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3170]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3170 : work3170.theta.ok = true ∧
    work3170.jac.invOK = true ∧ acceptsUnitSq work3170.out = true := by decide +kernel

def cell3170 : CellCertificate where
  tauBall := tau3170
  contactCenter := center3170
  contactBall := contact3170
  work := work3170
  center_sq := center_sq3170
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3170.1
  jac_ok := checks3170.2.1
  accepted := checks3170.2.2

def tau3171 : RatBall :=
  ⟨⟨23/128, -227/640⟩, 3/1280⟩
def center3171 : GaussianRat :=
  ⟨140448677/1000000000, -247117293/1000000000⟩
def contact3171 : RatBall := localContactBall tau3171 center3171
def work3171 : RoundedTauEval :=
  evalTau precision tau3171 contact3171 logTwoBall

theorem center_sq3171 : (center3171.re : ℝ)^2 +
    (center3171.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3171]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3171 : work3171.theta.ok = true ∧
    work3171.jac.invOK = true ∧ acceptsUnitSq work3171.out = true := by decide +kernel

def cell3171 : CellCertificate where
  tauBall := tau3171
  contactCenter := center3171
  contactBall := contact3171
  work := work3171
  center_sq := center_sq3171
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3171.1
  jac_ok := checks3171.2.1
  accepted := checks3171.2.2

def tau3172 : RatBall :=
  ⟨⟨113/640, -45/128⟩, 3/1280⟩
def center3172 : GaussianRat :=
  ⟨137760383/1000000000, -245107147/1000000000⟩
def contact3172 : RatBall := localContactBall tau3172 center3172
def work3172 : RoundedTauEval :=
  evalTau precision tau3172 contact3172 logTwoBall

theorem center_sq3172 : (center3172.re : ℝ)^2 +
    (center3172.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3172]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396


