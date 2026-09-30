-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0405
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0405
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:31:35.218519+00:00
-- url     : https://prove2.me/theorems/e8c03e64-a869-4a79-8f1c-3d066b02acd4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0405` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0405` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0405` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0405 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0405.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0405 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0405

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3240 : RatBall :=
  ⟨⟨-113/640, 229/640⟩, 3/1280⟩
def center3240 : GaussianRat :=
  ⟨-69219087/500000000, 49963011/200000000⟩
def contact3240 : RatBall := localContactBall tau3240 center3240
def work3240 : RoundedTauEval :=
  evalTau precision tau3240 contact3240 logTwoBall

theorem center_sq3240 : (center3240.re : ℝ)^2 +
    (center3240.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3240]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3240 : work3240.theta.ok = true ∧
    work3240.jac.invOK = true ∧ acceptsUnitSq work3240.out = true := by decide +kernel

def cell3240 : CellCertificate where
  tauBall := tau3240
  contactCenter := center3240
  contactBall := contact3240
  work := work3240
  center_sq := center_sq3240
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3240.1
  jac_ok := checks3240.2.1
  accepted := checks3240.2.2

def tau3241 : RatBall :=
  ⟨⟨-113/640, 231/640⟩, 3/1280⟩
def center3241 : GaussianRat :=
  ⟨-138783923/1000000000, 252176463/1000000000⟩
def contact3241 : RatBall := localContactBall tau3241 center3241
def work3241 : RoundedTauEval :=
  evalTau precision tau3241 contact3241 logTwoBall

theorem center_sq3241 : (center3241.re : ℝ)^2 +
    (center3241.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3241]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3241 : work3241.theta.ok = true ∧
    work3241.jac.invOK = true ∧ acceptsUnitSq work3241.out = true := by decide +kernel

def cell3241 : CellCertificate where
  tauBall := tau3241
  contactCenter := center3241
  contactBall := contact3241
  work := work3241
  center_sq := center_sq3241
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3241.1
  jac_ok := checks3241.2.1
  accepted := checks3241.2.2

def tau3242 : RatBall :=
  ⟨⟨-111/640, 45/128⟩, 3/1280⟩
def center3242 : GaussianRat :=
  ⟨-67704553/500000000, 6135977/25000000⟩
def contact3242 : RatBall := localContactBall tau3242 center3242
def work3242 : RoundedTauEval :=
  evalTau precision tau3242 contact3242 logTwoBall

theorem center_sq3242 : (center3242.re : ℝ)^2 +
    (center3242.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3242]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3242 : work3242.theta.ok = true ∧
    work3242.jac.invOK = true ∧ acceptsUnitSq work3242.out = true := by decide +kernel

def cell3242 : CellCertificate where
  tauBall := tau3242
  contactCenter := center3242
  contactBall := contact3242
  work := work3242
  center_sq := center_sq3242
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3242.1
  jac_ok := checks3242.2.1
  accepted := checks3242.2.2

def tau3243 : RatBall :=
  ⟨⟨-109/640, 45/128⟩, 3/1280⟩
def center3243 : GaussianRat :=
  ⟨-26610681/200000000, 245766093/1000000000⟩
def contact3243 : RatBall := localContactBall tau3243 center3243
def work3243 : RoundedTauEval :=
  evalTau precision tau3243 contact3243 logTwoBall

theorem center_sq3243 : (center3243.re : ℝ)^2 +
    (center3243.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3243]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3243 : work3243.theta.ok = true ∧
    work3243.jac.invOK = true ∧ acceptsUnitSq work3243.out = true := by decide +kernel

def cell3243 : CellCertificate where
  tauBall := tau3243
  contactCenter := center3243
  contactBall := contact3243
  work := work3243
  center_sq := center_sq3243
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3243.1
  jac_ok := checks3243.2.1
  accepted := checks3243.2.2

def tau3244 : RatBall :=
  ⟨⟨-111/640, 227/640⟩, 3/1280⟩
def center3244 : GaussianRat :=
  ⟨-135740809/1000000000, 4955901/20000000⟩
def contact3244 : RatBall := localContactBall tau3244 center3244
def work3244 : RoundedTauEval :=
  evalTau precision tau3244 contact3244 logTwoBall

theorem center_sq3244 : (center3244.re : ℝ)^2 +
    (center3244.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3244]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3244 : work3244.theta.ok = true ∧
    work3244.jac.invOK = true ∧ acceptsUnitSq work3244.out = true := by decide +kernel

def cell3244 : CellCertificate where
  tauBall := tau3244
  contactCenter := center3244
  contactBall := contact3244
  work := work3244
  center_sq := center_sq3244
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3244.1
  jac_ok := checks3244.2.1
  accepted := checks3244.2.2

def tau3245 : RatBall :=
  ⟨⟨-109/640, 227/640⟩, 3/1280⟩
def center3245 : GaussianRat :=
  ⟨-133380131/1000000000, 248126483/1000000000⟩
def contact3245 : RatBall := localContactBall tau3245 center3245
def work3245 : RoundedTauEval :=
  evalTau precision tau3245 contact3245 logTwoBall

theorem center_sq3245 : (center3245.re : ℝ)^2 +
    (center3245.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3245]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3245 : work3245.theta.ok = true ∧
    work3245.jac.invOK = true ∧ acceptsUnitSq work3245.out = true := by decide +kernel

def cell3245 : CellCertificate where
  tauBall := tau3245
  contactCenter := center3245
  contactBall := contact3245
  work := work3245
  center_sq := center_sq3245
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3245.1
  jac_ok := checks3245.2.1
  accepted := checks3245.2.2

def tau3246 : RatBall :=
  ⟨⟨-111/640, 229/640⟩, 3/1280⟩
def center3246 : GaussianRat :=
  ⟨-136076987/1000000000, 250155999/1000000000⟩
def contact3246 : RatBall := localContactBall tau3246 center3246
def work3246 : RoundedTauEval :=
  evalTau precision tau3246 contact3246 logTwoBall

theorem center_sq3246 : (center3246.re : ℝ)^2 +
    (center3246.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3246]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3246 : work3246.theta.ok = true ∧
    work3246.jac.invOK = true ∧ acceptsUnitSq work3246.out = true := by decide +kernel

def cell3246 : CellCertificate where
  tauBall := tau3246
  contactCenter := center3246
  contactBall := contact3246
  work := work3246
  center_sq := center_sq3246
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3246.1
  jac_ok := checks3246.2.1
  accepted := checks3246.2.2

def tau3247 : RatBall :=
  ⟨⟨-109/640, 229/640⟩, 3/1280⟩
def center3247 : GaussianRat :=
  ⟨-133711273/1000000000, 250491903/1000000000⟩
def contact3247 : RatBall := localContactBall tau3247 center3247
def work3247 : RoundedTauEval :=
  evalTau precision tau3247 contact3247 logTwoBall

theorem center_sq3247 : (center3247.re : ℝ)^2 +
    (center3247.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3247]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3247 : work3247.theta.ok = true ∧
    work3247.jac.invOK = true ∧ acceptsUnitSq work3247.out = true := by decide +kernel

def cell3247 : CellCertificate where
  tauBall := tau3247
  contactCenter := center3247
  contactBall := contact3247
  work := work3247
  center_sq := center_sq3247
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3247.1
  jac_ok := checks3247.2.1
  accepted := checks3247.2.2

def cells : List CellCertificate := [cell3240, cell3241, cell3242, cell3243, cell3244, cell3245, cell3246, cell3247]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0405

end


