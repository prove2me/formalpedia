-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0379_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0379_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:42:46.984297+00:00
-- url     : https://prove2.me/theorems/f1d68da7-df2e-41ec-8080-44c7fab9cfd4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0379 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3032 : RatBall :=
  ⟨⟨59/640, -247/640⟩, 3/1280⟩
def center3032 : GaussianRat :=
  ⟨75128671/1000000000, -55898717/200000000⟩
def contact3032 : RatBall := localContactBall tau3032 center3032
def work3032 : RoundedTauEval :=
  evalTau precision tau3032 contact3032 logTwoBall

theorem center_sq3032 : (center3032.re : ℝ)^2 +
    (center3032.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3032]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3032 : work3032.theta.ok = true ∧
    work3032.jac.invOK = true ∧ acceptsUnitSq work3032.out = true := by decide +kernel

def cell3032 : CellCertificate where
  tauBall := tau3032
  contactCenter := center3032
  contactBall := contact3032
  work := work3032
  center_sq := center_sq3032
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3032.1
  jac_ok := checks3032.2.1
  accepted := checks3032.2.2

def tau3033 : RatBall :=
  ⟨⟨57/640, -49/128⟩, 3/1280⟩
def center3033 : GaussianRat :=
  ⟨7240167/100000000, -277190643/1000000000⟩
def contact3033 : RatBall := localContactBall tau3033 center3033
def work3033 : RoundedTauEval :=
  evalTau precision tau3033 contact3033 logTwoBall

theorem center_sq3033 : (center3033.re : ℝ)^2 +
    (center3033.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3033]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3033 : work3033.theta.ok = true ∧
    work3033.jac.invOK = true ∧ acceptsUnitSq work3033.out = true := by decide +kernel

def cell3033 : CellCertificate where
  tauBall := tau3033
  contactCenter := center3033
  contactBall := contact3033
  work := work3033
  center_sq := center_sq3033
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3033.1
  jac_ok := checks3033.2.1
  accepted := checks3033.2.2

def tau3034 : RatBall :=
  ⟨⟨59/640, -49/128⟩, 3/1280⟩
def center3034 : GaussianRat :=
  ⟨7491319/100000000, -34622509/125000000⟩
def contact3034 : RatBall := localContactBall tau3034 center3034
def work3034 : RoundedTauEval :=
  evalTau precision tau3034 contact3034 logTwoBall

theorem center_sq3034 : (center3034.re : ℝ)^2 +
    (center3034.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3034]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3034 : work3034.theta.ok = true ∧
    work3034.jac.invOK = true ∧ acceptsUnitSq work3034.out = true := by decide +kernel

def cell3034 : CellCertificate where
  tauBall := tau3034
  contactCenter := center3034
  contactBall := contact3034
  work := work3034
  center_sq := center_sq3034
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3034.1
  jac_ok := checks3034.2.1
  accepted := checks3034.2.2

def tau3035 : RatBall :=
  ⟨⟨61/640, -247/640⟩, 3/1280⟩
def center3035 : GaussianRat :=
  ⟨77644141/1000000000, -139636577/500000000⟩
def contact3035 : RatBall := localContactBall tau3035 center3035
def work3035 : RoundedTauEval :=
  evalTau precision tau3035 contact3035 logTwoBall

theorem center_sq3035 : (center3035.re : ℝ)^2 +
    (center3035.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3035]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3035 : work3035.theta.ok = true ∧
    work3035.jac.invOK = true ∧ acceptsUnitSq work3035.out = true := by decide +kernel

def cell3035 : CellCertificate where
  tauBall := tau3035
  contactCenter := center3035
  contactBall := contact3035
  work := work3035
  center_sq := center_sq3035
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3035.1
  jac_ok := checks3035.2.1
  accepted := checks3035.2.2

def tau3036 : RatBall :=
  ⟨⟨63/640, -247/640⟩, 3/1280⟩
def center3036 : GaussianRat :=
  ⟨40078273/500000000, -69761453/250000000⟩
def contact3036 : RatBall := localContactBall tau3036 center3036
def work3036 : RoundedTauEval :=
  evalTau precision tau3036 contact3036 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379


