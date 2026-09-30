-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0406
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0406
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:29:17.15561+00:00
-- url     : https://prove2.me/theorems/963515c9-d861-4a16-994d-e87ca5a10d55
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0406` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0406` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0406` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0406 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0406.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0406 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0406

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3248 : RatBall :=
  ⟨⟨-111/640, 231/640⟩, 3/1280⟩
def center3248 : GaussianRat :=
  ⟨-34104423/250000000, 25252199/100000000⟩
def contact3248 : RatBall := localContactBall tau3248 center3248
def work3248 : RoundedTauEval :=
  evalTau precision tau3248 contact3248 logTwoBall

theorem center_sq3248 : (center3248.re : ℝ)^2 +
    (center3248.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3248]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3248 : work3248.theta.ok = true ∧
    work3248.jac.invOK = true ∧ acceptsUnitSq work3248.out = true := by decide +kernel

def cell3248 : CellCertificate where
  tauBall := tau3248
  contactCenter := center3248
  contactBall := contact3248
  work := work3248
  center_sq := center_sq3248
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3248.1
  jac_ok := checks3248.2.1
  accepted := checks3248.2.2

def tau3249 : RatBall :=
  ⟨⟨-109/640, 231/640⟩, 3/1280⟩
def center3249 : GaussianRat :=
  ⟨-134046881/1000000000, 15803901/62500000⟩
def contact3249 : RatBall := localContactBall tau3249 center3249
def work3249 : RoundedTauEval :=
  evalTau precision tau3249 contact3249 logTwoBall

theorem center_sq3249 : (center3249.re : ℝ)^2 +
    (center3249.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3249]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3249 : work3249.theta.ok = true ∧
    work3249.jac.invOK = true ∧ acceptsUnitSq work3249.out = true := by decide +kernel

def cell3249 : CellCertificate where
  tauBall := tau3249
  contactCenter := center3249
  contactBall := contact3249
  work := work3249
  center_sq := center_sq3249
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3249.1
  jac_ok := checks3249.2.1
  accepted := checks3249.2.2

def tau3250 : RatBall :=
  ⟨⟨-107/640, 229/640⟩, 3/1280⟩
def center3250 : GaussianRat :=
  ⟨-65670547/500000000, 62705679/250000000⟩
def contact3250 : RatBall := localContactBall tau3250 center3250
def work3250 : RoundedTauEval :=
  evalTau precision tau3250 contact3250 logTwoBall

theorem center_sq3250 : (center3250.re : ℝ)^2 +
    (center3250.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3250]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3250 : work3250.theta.ok = true ∧
    work3250.jac.invOK = true ∧ acceptsUnitSq work3250.out = true := by decide +kernel

def cell3250 : CellCertificate where
  tauBall := tau3250
  contactCenter := center3250
  contactBall := contact3250
  work := work3250
  center_sq := center_sq3250
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3250.1
  jac_ok := checks3250.2.1
  accepted := checks3250.2.2

def tau3251 : RatBall :=
  ⟨⟨-21/128, 229/640⟩, 3/1280⟩
def center3251 : GaussianRat :=
  ⟨-128966511/1000000000, 50229677/200000000⟩
def contact3251 : RatBall := localContactBall tau3251 center3251
def work3251 : RoundedTauEval :=
  evalTau precision tau3251 contact3251 logTwoBall

theorem center_sq3251 : (center3251.re : ℝ)^2 +
    (center3251.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3251]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3251 : work3251.theta.ok = true ∧
    work3251.jac.invOK = true ∧ acceptsUnitSq work3251.out = true := by decide +kernel

def cell3251 : CellCertificate where
  tauBall := tau3251
  contactCenter := center3251
  contactBall := contact3251
  work := work3251
  center_sq := center_sq3251
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3251.1
  jac_ok := checks3251.2.1
  accepted := checks3251.2.2

def tau3252 : RatBall :=
  ⟨⟨-107/640, 231/640⟩, 3/1280⟩
def center3252 : GaussianRat :=
  ⟨-65835777/500000000, 253197689/1000000000⟩
def contact3252 : RatBall := localContactBall tau3252 center3252
def work3252 : RoundedTauEval :=
  evalTau precision tau3252 contact3252 logTwoBall

theorem center_sq3252 : (center3252.re : ℝ)^2 +
    (center3252.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3252]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3252 : work3252.theta.ok = true ∧
    work3252.jac.invOK = true ∧ acceptsUnitSq work3252.out = true := by decide +kernel

def cell3252 : CellCertificate where
  tauBall := tau3252
  contactCenter := center3252
  contactBall := contact3252
  work := work3252
  center_sq := center_sq3252
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3252.1
  jac_ok := checks3252.2.1
  accepted := checks3252.2.2

def tau3253 : RatBall :=
  ⟨⟨-21/128, 231/640⟩, 3/1280⟩
def center3253 : GaussianRat :=
  ⟨-32322943/250000000, 63381939/250000000⟩
def contact3253 : RatBall := localContactBall tau3253 center3253
def work3253 : RoundedTauEval :=
  evalTau precision tau3253 contact3253 logTwoBall

theorem center_sq3253 : (center3253.re : ℝ)^2 +
    (center3253.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3253]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3253 : work3253.theta.ok = true ∧
    work3253.jac.invOK = true ∧ acceptsUnitSq work3253.out = true := by decide +kernel

def cell3253 : CellCertificate where
  tauBall := tau3253
  contactCenter := center3253
  contactBall := contact3253
  work := work3253
  center_sq := center_sq3253
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3253.1
  jac_ok := checks3253.2.1
  accepted := checks3253.2.2

def tau3254 : RatBall :=
  ⟨⟨-103/640, 229/640⟩, 3/1280⟩
def center3254 : GaussianRat :=
  ⟨-126587587/1000000000, 125734431/500000000⟩
def contact3254 : RatBall := localContactBall tau3254 center3254
def work3254 : RoundedTauEval :=
  evalTau precision tau3254 contact3254 logTwoBall

theorem center_sq3254 : (center3254.re : ℝ)^2 +
    (center3254.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3254]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3254 : work3254.theta.ok = true ∧
    work3254.jac.invOK = true ∧ acceptsUnitSq work3254.out = true := by decide +kernel

def cell3254 : CellCertificate where
  tauBall := tau3254
  contactCenter := center3254
  contactBall := contact3254
  work := work3254
  center_sq := center_sq3254
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3254.1
  jac_ok := checks3254.2.1
  accepted := checks3254.2.2

def tau3255 : RatBall :=
  ⟨⟨-101/640, 229/640⟩, 3/1280⟩
def center3255 : GaussianRat :=
  ⟨-62102193/500000000, 7868253/31250000⟩
def contact3255 : RatBall := localContactBall tau3255 center3255
def work3255 : RoundedTauEval :=
  evalTau precision tau3255 contact3255 logTwoBall

theorem center_sq3255 : (center3255.re : ℝ)^2 +
    (center3255.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3255]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3255 : work3255.theta.ok = true ∧
    work3255.jac.invOK = true ∧ acceptsUnitSq work3255.out = true := by decide +kernel

def cell3255 : CellCertificate where
  tauBall := tau3255
  contactCenter := center3255
  contactBall := contact3255
  work := work3255
  center_sq := center_sq3255
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3255.1
  jac_ok := checks3255.2.1
  accepted := checks3255.2.2

def cells : List CellCertificate := [cell3248, cell3249, cell3250, cell3251, cell3252, cell3253, cell3254, cell3255]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0406

end


