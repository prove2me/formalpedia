-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0389_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0389_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:04:37.515832+00:00
-- url     : https://prove2.me/theorems/c9480bb6-cf6c-4943-aac8-4330cb9f8b74
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0389 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3112 : RatBall :=
  ⟨⟨87/640, -233/640⟩, 3/1280⟩
def center3112 : GaussianRat :=
  ⟨10796407/100000000, -129338763/500000000⟩
def contact3112 : RatBall := localContactBall tau3112 center3112
def work3112 : RoundedTauEval :=
  evalTau precision tau3112 contact3112 logTwoBall

theorem center_sq3112 : (center3112.re : ℝ)^2 +
    (center3112.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3112]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3112 : work3112.theta.ok = true ∧
    work3112.jac.invOK = true ∧ acceptsUnitSq work3112.out = true := by decide +kernel

def cell3112 : CellCertificate where
  tauBall := tau3112
  contactCenter := center3112
  contactBall := contact3112
  work := work3112
  center_sq := center_sq3112
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3112.1
  jac_ok := checks3112.2.1
  accepted := checks3112.2.2

def tau3113 : RatBall :=
  ⟨⟨89/640, -239/640⟩, 3/1280⟩
def center3113 : GaussianRat :=
  ⟨111267493/1000000000, -265680799/1000000000⟩
def contact3113 : RatBall := localContactBall tau3113 center3113
def work3113 : RoundedTauEval :=
  evalTau precision tau3113 contact3113 logTwoBall

theorem center_sq3113 : (center3113.re : ℝ)^2 +
    (center3113.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3113]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3113 : work3113.theta.ok = true ∧
    work3113.jac.invOK = true ∧ acceptsUnitSq work3113.out = true := by decide +kernel

def cell3113 : CellCertificate where
  tauBall := tau3113
  contactCenter := center3113
  contactBall := contact3113
  work := work3113
  center_sq := center_sq3113
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3113.1
  jac_ok := checks3113.2.1
  accepted := checks3113.2.2

def tau3114 : RatBall :=
  ⟨⟨91/640, -239/640⟩, 3/1280⟩
def center3114 : GaussianRat :=
  ⟨113703619/1000000000, -265378247/1000000000⟩
def contact3114 : RatBall := localContactBall tau3114 center3114
def work3114 : RoundedTauEval :=
  evalTau precision tau3114 contact3114 logTwoBall

theorem center_sq3114 : (center3114.re : ℝ)^2 +
    (center3114.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3114]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3114 : work3114.theta.ok = true ∧
    work3114.jac.invOK = true ∧ acceptsUnitSq work3114.out = true := by decide +kernel

def cell3114 : CellCertificate where
  tauBall := tau3114
  contactCenter := center3114
  contactBall := contact3114
  work := work3114
  center_sq := center_sq3114
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3114.1
  jac_ok := checks3114.2.1
  accepted := checks3114.2.2

def tau3115 : RatBall :=
  ⟨⟨89/640, -237/640⟩, 3/1280⟩
def center3115 : GaussianRat :=
  ⟨55484957/500000000, -65811399/250000000⟩
def contact3115 : RatBall := localContactBall tau3115 center3115
def work3115 : RoundedTauEval :=
  evalTau precision tau3115 contact3115 logTwoBall

theorem center_sq3115 : (center3115.re : ℝ)^2 +
    (center3115.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3115]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3115 : work3115.theta.ok = true ∧
    work3115.jac.invOK = true ∧ acceptsUnitSq work3115.out = true := by decide +kernel

def cell3115 : CellCertificate where
  tauBall := tau3115
  contactCenter := center3115
  contactBall := contact3115
  work := work3115
  center_sq := center_sq3115
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3115.1
  jac_ok := checks3115.2.1
  accepted := checks3115.2.2

def tau3116 : RatBall :=
  ⟨⟨91/640, -237/640⟩, 3/1280⟩
def center3116 : GaussianRat :=
  ⟨22680033/200000000, -131473549/500000000⟩
def contact3116 : RatBall := localContactBall tau3116 center3116

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389


