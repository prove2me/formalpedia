-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0388
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0388
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:26:34.02787+00:00
-- url     : https://prove2.me/theorems/aa635e07-a9fa-40f5-b285-06c19f370f5a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0388` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0388` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0388` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0388 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0388.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0388 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0388

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3104 : RatBall :=
  ⟨⟨87/640, -237/640⟩, 3/1280⟩
def center3104 : GaussianRat :=
  ⟨108535671/1000000000, -263538231/1000000000⟩
def contact3104 : RatBall := localContactBall tau3104 center3104
def work3104 : RoundedTauEval :=
  evalTau precision tau3104 contact3104 logTwoBall

theorem center_sq3104 : (center3104.re : ℝ)^2 +
    (center3104.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3104]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3104 : work3104.theta.ok = true ∧
    work3104.jac.invOK = true ∧ acceptsUnitSq work3104.out = true := by decide +kernel

def cell3104 : CellCertificate where
  tauBall := tau3104
  contactCenter := center3104
  contactBall := contact3104
  work := work3104
  center_sq := center_sq3104
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3104.1
  jac_ok := checks3104.2.1
  accepted := checks3104.2.2

def tau3105 : RatBall :=
  ⟨⟨81/640, -47/128⟩, 3/1280⟩
def center3105 : GaussianRat :=
  ⟨100939831/1000000000, -261935857/1000000000⟩
def contact3105 : RatBall := localContactBall tau3105 center3105
def work3105 : RoundedTauEval :=
  evalTau precision tau3105 contact3105 logTwoBall

theorem center_sq3105 : (center3105.re : ℝ)^2 +
    (center3105.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3105]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3105 : work3105.theta.ok = true ∧
    work3105.jac.invOK = true ∧ acceptsUnitSq work3105.out = true := by decide +kernel

def cell3105 : CellCertificate where
  tauBall := tau3105
  contactCenter := center3105
  contactBall := contact3105
  work := work3105
  center_sq := center_sq3105
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3105.1
  jac_ok := checks3105.2.1
  accepted := checks3105.2.2

def tau3106 : RatBall :=
  ⟨⟨83/640, -47/128⟩, 3/1280⟩
def center3106 : GaussianRat :=
  ⟨25844903/250000000, -261664807/1000000000⟩
def contact3106 : RatBall := localContactBall tau3106 center3106
def work3106 : RoundedTauEval :=
  evalTau precision tau3106 contact3106 logTwoBall

theorem center_sq3106 : (center3106.re : ℝ)^2 +
    (center3106.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3106]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3106 : work3106.theta.ok = true ∧
    work3106.jac.invOK = true ∧ acceptsUnitSq work3106.out = true := by decide +kernel

def cell3106 : CellCertificate where
  tauBall := tau3106
  contactCenter := center3106
  contactBall := contact3106
  work := work3106
  center_sq := center_sq3106
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3106.1
  jac_ok := checks3106.2.1
  accepted := checks3106.2.2

def tau3107 : RatBall :=
  ⟨⟨81/640, -233/640⟩, 3/1280⟩
def center3107 : GaussianRat :=
  ⟨12584197/125000000, -1013661/3906250⟩
def contact3107 : RatBall := localContactBall tau3107 center3107
def work3107 : RoundedTauEval :=
  evalTau precision tau3107 contact3107 logTwoBall

theorem center_sq3107 : (center3107.re : ℝ)^2 +
    (center3107.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3107]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3107 : work3107.theta.ok = true ∧
    work3107.jac.invOK = true ∧ acceptsUnitSq work3107.out = true := by decide +kernel

def cell3107 : CellCertificate where
  tauBall := tau3107
  contactCenter := center3107
  contactBall := contact3107
  work := work3107
  center_sq := center_sq3107
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3107.1
  jac_ok := checks3107.2.1
  accepted := checks3107.2.2

def tau3108 : RatBall :=
  ⟨⟨83/640, -233/640⟩, 3/1280⟩
def center3108 : GaussianRat :=
  ⟨103107441/1000000000, -129614913/500000000⟩
def contact3108 : RatBall := localContactBall tau3108 center3108
def work3108 : RoundedTauEval :=
  evalTau precision tau3108 contact3108 logTwoBall

theorem center_sq3108 : (center3108.re : ℝ)^2 +
    (center3108.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3108]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3108 : work3108.theta.ok = true ∧
    work3108.jac.invOK = true ∧ acceptsUnitSq work3108.out = true := by decide +kernel

def cell3108 : CellCertificate where
  tauBall := tau3108
  contactCenter := center3108
  contactBall := contact3108
  work := work3108
  center_sq := center_sq3108
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3108.1
  jac_ok := checks3108.2.1
  accepted := checks3108.2.2

def tau3109 : RatBall :=
  ⟨⟨17/128, -47/128⟩, 3/1280⟩
def center3109 : GaussianRat :=
  ⟨13226959/125000000, -130693913/500000000⟩
def contact3109 : RatBall := localContactBall tau3109 center3109
def work3109 : RoundedTauEval :=
  evalTau precision tau3109 contact3109 logTwoBall

theorem center_sq3109 : (center3109.re : ℝ)^2 +
    (center3109.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3109]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3109 : work3109.theta.ok = true ∧
    work3109.jac.invOK = true ∧ acceptsUnitSq work3109.out = true := by decide +kernel

def cell3109 : CellCertificate where
  tauBall := tau3109
  contactCenter := center3109
  contactBall := contact3109
  work := work3109
  center_sq := center_sq3109
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3109.1
  jac_ok := checks3109.2.1
  accepted := checks3109.2.2

def tau3110 : RatBall :=
  ⟨⟨87/640, -47/128⟩, 3/1280⟩
def center3110 : GaussianRat :=
  ⟨21649587/200000000, -815953/3125000⟩
def contact3110 : RatBall := localContactBall tau3110 center3110
def work3110 : RoundedTauEval :=
  evalTau precision tau3110 contact3110 logTwoBall

theorem center_sq3110 : (center3110.re : ℝ)^2 +
    (center3110.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3110]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3110 : work3110.theta.ok = true ∧
    work3110.jac.invOK = true ∧ acceptsUnitSq work3110.out = true := by decide +kernel

def cell3110 : CellCertificate where
  tauBall := tau3110
  contactCenter := center3110
  contactBall := contact3110
  work := work3110
  center_sq := center_sq3110
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3110.1
  jac_ok := checks3110.2.1
  accepted := checks3110.2.2

def tau3111 : RatBall :=
  ⟨⟨17/128, -233/640⟩, 3/1280⟩
def center3111 : GaussianRat :=
  ⟨105537631/1000000000, -258956581/1000000000⟩
def contact3111 : RatBall := localContactBall tau3111 center3111
def work3111 : RoundedTauEval :=
  evalTau precision tau3111 contact3111 logTwoBall

theorem center_sq3111 : (center3111.re : ℝ)^2 +
    (center3111.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3111]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3111 : work3111.theta.ok = true ∧
    work3111.jac.invOK = true ∧ acceptsUnitSq work3111.out = true := by decide +kernel

def cell3111 : CellCertificate where
  tauBall := tau3111
  contactCenter := center3111
  contactBall := contact3111
  work := work3111
  center_sq := center_sq3111
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3111.1
  jac_ok := checks3111.2.1
  accepted := checks3111.2.2

def cells : List CellCertificate := [cell3104, cell3105, cell3106, cell3107, cell3108, cell3109, cell3110, cell3111]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0388

end


