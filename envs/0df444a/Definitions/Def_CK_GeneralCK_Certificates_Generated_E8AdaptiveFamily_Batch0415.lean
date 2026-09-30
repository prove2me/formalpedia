-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0415
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0415
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:58:19.925959+00:00
-- url     : https://prove2.me/theorems/f14fa738-0a90-4012-acc5-36bea6287fcf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0415` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0415` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0415` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0415 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0415.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0415 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0415

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3320 : RatBall :=
  ⟨⟨-69/640, 237/640⟩, 3/1280⟩
def center3320 : GaussianRat :=
  ⟨-86460351/1000000000, 265900339/1000000000⟩
def contact3320 : RatBall := localContactBall tau3320 center3320
def work3320 : RoundedTauEval :=
  evalTau precision tau3320 contact3320 logTwoBall

theorem center_sq3320 : (center3320.re : ℝ)^2 +
    (center3320.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3320]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3320 : work3320.theta.ok = true ∧
    work3320.jac.invOK = true ∧ acceptsUnitSq work3320.out = true := by decide +kernel

def cell3320 : CellCertificate where
  tauBall := tau3320
  contactCenter := center3320
  contactBall := contact3320
  work := work3320
  center_sq := center_sq3320
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3320.1
  jac_ok := checks3320.2.1
  accepted := checks3320.2.2

def tau3321 : RatBall :=
  ⟨⟨-71/640, 239/640⟩, 3/1280⟩
def center3321 : GaussianRat :=
  ⟨-89169649/1000000000, 67032703/250000000⟩
def contact3321 : RatBall := localContactBall tau3321 center3321
def work3321 : RoundedTauEval :=
  evalTau precision tau3321 contact3321 logTwoBall

theorem center_sq3321 : (center3321.re : ℝ)^2 +
    (center3321.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3321]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3321 : work3321.theta.ok = true ∧
    work3321.jac.invOK = true ∧ acceptsUnitSq work3321.out = true := by decide +kernel

def cell3321 : CellCertificate where
  tauBall := tau3321
  contactCenter := center3321
  contactBall := contact3321
  work := work3321
  center_sq := center_sq3321
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3321.1
  jac_ok := checks3321.2.1
  accepted := checks3321.2.2

def tau3322 : RatBall :=
  ⟨⟨-69/640, 239/640⟩, 3/1280⟩
def center3322 : GaussianRat :=
  ⟨-43348293/500000000, 268371857/1000000000⟩
def contact3322 : RatBall := localContactBall tau3322 center3322
def work3322 : RoundedTauEval :=
  evalTau precision tau3322 contact3322 logTwoBall

theorem center_sq3322 : (center3322.re : ℝ)^2 +
    (center3322.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3322]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3322 : work3322.theta.ok = true ∧
    work3322.jac.invOK = true ∧ acceptsUnitSq work3322.out = true := by decide +kernel

def cell3322 : CellCertificate where
  tauBall := tau3322
  contactCenter := center3322
  contactBall := contact3322
  work := work3322
  center_sq := center_sq3322
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3322.1
  jac_ok := checks3322.2.1
  accepted := checks3322.2.2

def tau3323 : RatBall :=
  ⟨⟨-67/640, 237/640⟩, 3/1280⟩
def center3323 : GaussianRat :=
  ⟨-20997603/250000000, 266131799/1000000000⟩
def contact3323 : RatBall := localContactBall tau3323 center3323
def work3323 : RoundedTauEval :=
  evalTau precision tau3323 contact3323 logTwoBall

theorem center_sq3323 : (center3323.re : ℝ)^2 +
    (center3323.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3323]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3323 : work3323.theta.ok = true ∧
    work3323.jac.invOK = true ∧ acceptsUnitSq work3323.out = true := by decide +kernel

def cell3323 : CellCertificate where
  tauBall := tau3323
  contactCenter := center3323
  contactBall := contact3323
  work := work3323
  center_sq := center_sq3323
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3323.1
  jac_ok := checks3323.2.1
  accepted := checks3323.2.2

def tau3324 : RatBall :=
  ⟨⟨-13/128, 237/640⟩, 3/1280⟩
def center3324 : GaussianRat :=
  ⟨-40758673/500000000, 133178453/500000000⟩
def contact3324 : RatBall := localContactBall tau3324 center3324
def work3324 : RoundedTauEval :=
  evalTau precision tau3324 contact3324 logTwoBall

theorem center_sq3324 : (center3324.re : ℝ)^2 +
    (center3324.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3324]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3324 : work3324.theta.ok = true ∧
    work3324.jac.invOK = true ∧ acceptsUnitSq work3324.out = true := by decide +kernel

def cell3324 : CellCertificate where
  tauBall := tau3324
  contactCenter := center3324
  contactBall := contact3324
  work := work3324
  center_sq := center_sq3324
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3324.1
  jac_ok := checks3324.2.1
  accepted := checks3324.2.2

def tau3325 : RatBall :=
  ⟨⟨-67/640, 239/640⟩, 3/1280⟩
def center3325 : GaussianRat :=
  ⟨-5263767/62500000, 134303253/500000000⟩
def contact3325 : RatBall := localContactBall tau3325 center3325
def work3325 : RoundedTauEval :=
  evalTau precision tau3325 contact3325 logTwoBall

theorem center_sq3325 : (center3325.re : ℝ)^2 +
    (center3325.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3325]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3325 : work3325.theta.ok = true ∧
    work3325.jac.invOK = true ∧ acceptsUnitSq work3325.out = true := by decide +kernel

def cell3325 : CellCertificate where
  tauBall := tau3325
  contactCenter := center3325
  contactBall := contact3325
  work := work3325
  center_sq := center_sq3325
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3325.1
  jac_ok := checks3325.2.1
  accepted := checks3325.2.2

def tau3326 : RatBall :=
  ⟨⟨-13/128, 239/640⟩, 3/1280⟩
def center3326 : GaussianRat :=
  ⟨-81740791/1000000000, 268834717/1000000000⟩
def contact3326 : RatBall := localContactBall tau3326 center3326
def work3326 : RoundedTauEval :=
  evalTau precision tau3326 contact3326 logTwoBall

theorem center_sq3326 : (center3326.re : ℝ)^2 +
    (center3326.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3326]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3326 : work3326.theta.ok = true ∧
    work3326.jac.invOK = true ∧ acceptsUnitSq work3326.out = true := by decide +kernel

def cell3326 : CellCertificate where
  tauBall := tau3326
  contactCenter := center3326
  contactBall := contact3326
  work := work3326
  center_sq := center_sq3326
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3326.1
  jac_ok := checks3326.2.1
  accepted := checks3326.2.2

def tau3327 : RatBall :=
  ⟨⟨-89/640, 241/640⟩, 3/1280⟩
def center3327 : GaussianRat :=
  ⟨-22313823/200000000, 13406097/50000000⟩
def contact3327 : RatBall := localContactBall tau3327 center3327
def work3327 : RoundedTauEval :=
  evalTau precision tau3327 contact3327 logTwoBall

theorem center_sq3327 : (center3327.re : ℝ)^2 +
    (center3327.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3327]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3327 : work3327.theta.ok = true ∧
    work3327.jac.invOK = true ∧ acceptsUnitSq work3327.out = true := by decide +kernel

def cell3327 : CellCertificate where
  tauBall := tau3327
  contactCenter := center3327
  contactBall := contact3327
  work := work3327
  center_sq := center_sq3327
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3327.1
  jac_ok := checks3327.2.1
  accepted := checks3327.2.2

def cells : List CellCertificate := [cell3320, cell3321, cell3322, cell3323, cell3324, cell3325, cell3326, cell3327]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0415

end


