-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0403
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0403
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:34:16.721346+00:00
-- url     : https://prove2.me/theorems/f196aa50-9752-48c7-9f68-9dae38b913b5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0403` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0403` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0403` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0403 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0403.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0403 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0403

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3224 : RatBall :=
  ⟨⟨-121/640, 221/640⟩, 3/1280⟩
def center3224 : GaussianRat :=
  ⟨-146422507/1000000000, 9563167/40000000⟩
def contact3224 : RatBall := localContactBall tau3224 center3224
def work3224 : RoundedTauEval :=
  evalTau precision tau3224 contact3224 logTwoBall

theorem center_sq3224 : (center3224.re : ℝ)^2 +
    (center3224.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3224]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3224 : work3224.theta.ok = true ∧
    work3224.jac.invOK = true ∧ acceptsUnitSq work3224.out = true := by decide +kernel

def cell3224 : CellCertificate where
  tauBall := tau3224
  contactCenter := center3224
  contactBall := contact3224
  work := work3224
  center_sq := center_sq3224
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3224.1
  jac_ok := checks3224.2.1
  accepted := checks3224.2.2

def tau3225 : RatBall :=
  ⟨⟨-123/640, 223/640⟩, 3/1280⟩
def center3225 : GaussianRat :=
  ⟨-74546313/500000000, 120525907/500000000⟩
def contact3225 : RatBall := localContactBall tau3225 center3225
def work3225 : RoundedTauEval :=
  evalTau precision tau3225 contact3225 logTwoBall

theorem center_sq3225 : (center3225.re : ℝ)^2 +
    (center3225.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3225]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3225 : work3225.theta.ok = true ∧
    work3225.jac.invOK = true ∧ acceptsUnitSq work3225.out = true := by decide +kernel

def cell3225 : CellCertificate where
  tauBall := tau3225
  contactCenter := center3225
  contactBall := contact3225
  work := work3225
  center_sq := center_sq3225
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3225.1
  jac_ok := checks3225.2.1
  accepted := checks3225.2.2

def tau3226 : RatBall :=
  ⟨⟨-121/640, 223/640⟩, 3/1280⟩
def center3226 : GaussianRat :=
  ⟨-146768957/1000000000, 60350721/250000000⟩
def contact3226 : RatBall := localContactBall tau3226 center3226
def work3226 : RoundedTauEval :=
  evalTau precision tau3226 contact3226 logTwoBall

theorem center_sq3226 : (center3226.re : ℝ)^2 +
    (center3226.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3226]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3226 : work3226.theta.ok = true ∧
    work3226.jac.invOK = true ∧ acceptsUnitSq work3226.out = true := by decide +kernel

def cell3226 : CellCertificate where
  tauBall := tau3226
  contactCenter := center3226
  contactBall := contact3226
  work := work3226
  center_sq := center_sq3226
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3226.1
  jac_ok := checks3226.2.1
  accepted := checks3226.2.2

def tau3227 : RatBall :=
  ⟨⟨-123/640, 45/128⟩, 3/1280⟩
def center3227 : GaussianRat :=
  ⟨-149448351/1000000000, 9735017/40000000⟩
def contact3227 : RatBall := localContactBall tau3227 center3227
def work3227 : RoundedTauEval :=
  evalTau precision tau3227 contact3227 logTwoBall

theorem center_sq3227 : (center3227.re : ℝ)^2 +
    (center3227.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3227]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3227 : work3227.theta.ok = true ∧
    work3227.jac.invOK = true ∧ acceptsUnitSq work3227.out = true := by decide +kernel

def cell3227 : CellCertificate where
  tauBall := tau3227
  contactCenter := center3227
  contactBall := contact3227
  work := work3227
  center_sq := center_sq3227
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3227.1
  jac_ok := checks3227.2.1
  accepted := checks3227.2.2

def tau3228 : RatBall :=
  ⟨⟨-121/640, 45/128⟩, 3/1280⟩
def center3228 : GaussianRat :=
  ⟨-36780017/250000000, 243731207/1000000000⟩
def contact3228 : RatBall := localContactBall tau3228 center3228
def work3228 : RoundedTauEval :=
  evalTau precision tau3228 contact3228 logTwoBall

theorem center_sq3228 : (center3228.re : ℝ)^2 +
    (center3228.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3228]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3228 : work3228.theta.ok = true ∧
    work3228.jac.invOK = true ∧ acceptsUnitSq work3228.out = true := by decide +kernel

def cell3228 : CellCertificate where
  tauBall := tau3228
  contactCenter := center3228
  contactBall := contact3228
  work := work3228
  center_sq := center_sq3228
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3228.1
  jac_ok := checks3228.2.1
  accepted := checks3228.2.2

def tau3229 : RatBall :=
  ⟨⟨-121/640, 227/640⟩, 3/1280⟩
def center3229 : GaussianRat :=
  ⟨-147475889/1000000000, 123032099/500000000⟩
def contact3229 : RatBall := localContactBall tau3229 center3229
def work3229 : RoundedTauEval :=
  evalTau precision tau3229 contact3229 logTwoBall

theorem center_sq3229 : (center3229.re : ℝ)^2 +
    (center3229.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3229]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3229 : work3229.theta.ok = true ∧
    work3229.jac.invOK = true ∧ acceptsUnitSq work3229.out = true := by decide +kernel

def cell3229 : CellCertificate where
  tauBall := tau3229
  contactCenter := center3229
  contactBall := contact3229
  work := work3229
  center_sq := center_sq3229
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3229.1
  jac_ok := checks3229.2.1
  accepted := checks3229.2.2

def tau3230 : RatBall :=
  ⟨⟨-119/640, 45/128⟩, 3/1280⟩
def center3230 : GaussianRat :=
  ⟨-72393537/500000000, 122041161/500000000⟩
def contact3230 : RatBall := localContactBall tau3230 center3230
def work3230 : RoundedTauEval :=
  evalTau precision tau3230 contact3230 logTwoBall

theorem center_sq3230 : (center3230.re : ℝ)^2 +
    (center3230.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3230]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3230 : work3230.theta.ok = true ∧
    work3230.jac.invOK = true ∧ acceptsUnitSq work3230.out = true := by decide +kernel

def cell3230 : CellCertificate where
  tauBall := tau3230
  contactCenter := center3230
  contactBall := contact3230
  work := work3230
  center_sq := center_sq3230
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3230.1
  jac_ok := checks3230.2.1
  accepted := checks3230.2.2

def tau3231 : RatBall :=
  ⟨⟨-117/640, 45/128⟩, 3/1280⟩
def center3231 : GaussianRat :=
  ⟨-8903089/62500000, 244428717/1000000000⟩
def contact3231 : RatBall := localContactBall tau3231 center3231
def work3231 : RoundedTauEval :=
  evalTau precision tau3231 contact3231 logTwoBall

theorem center_sq3231 : (center3231.re : ℝ)^2 +
    (center3231.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3231]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3231 : work3231.theta.ok = true ∧
    work3231.jac.invOK = true ∧ acceptsUnitSq work3231.out = true := by decide +kernel

def cell3231 : CellCertificate where
  tauBall := tau3231
  contactCenter := center3231
  contactBall := contact3231
  work := work3231
  center_sq := center_sq3231
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3231.1
  jac_ok := checks3231.2.1
  accepted := checks3231.2.2

def cells : List CellCertificate := [cell3224, cell3225, cell3226, cell3227, cell3228, cell3229, cell3230, cell3231]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0403

end


