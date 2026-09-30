-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0391_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0391_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:22:07.37466+00:00
-- url     : https://prove2.me/theorems/19411801-f079-41b0-9b9e-25f3db1f9ff9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0391 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3128 : RatBall :=
  ⟨⟨19/128, -233/640⟩, 3/1280⟩
def center3128 : GaussianRat :=
  ⟨7351929/62500000, -128752067/500000000⟩
def contact3128 : RatBall := localContactBall tau3128 center3128
def work3128 : RoundedTauEval :=
  evalTau precision tau3128 contact3128 logTwoBall

theorem center_sq3128 : (center3128.re : ℝ)^2 +
    (center3128.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3128]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3128 : work3128.theta.ok = true ∧
    work3128.jac.invOK = true ∧ acceptsUnitSq work3128.out = true := by decide +kernel

def cell3128 : CellCertificate where
  tauBall := tau3128
  contactCenter := center3128
  contactBall := contact3128
  work := work3128
  center_sq := center_sq3128
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3128.1
  jac_ok := checks3128.2.1
  accepted := checks3128.2.2

def tau3129 : RatBall :=
  ⟨⟨93/640, -231/640⟩, 3/1280⟩
def center3129 : GaussianRat :=
  ⟨114923139/1000000000, -12769801/50000000⟩
def contact3129 : RatBall := localContactBall tau3129 center3129
def work3129 : RoundedTauEval :=
  evalTau precision tau3129 contact3129 logTwoBall

theorem center_sq3129 : (center3129.re : ℝ)^2 +
    (center3129.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3129]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3129 : work3129.theta.ok = true ∧
    work3129.jac.invOK = true ∧ acceptsUnitSq work3129.out = true := by decide +kernel

def cell3129 : CellCertificate where
  tauBall := tau3129
  contactCenter := center3129
  contactBall := contact3129
  work := work3129
  center_sq := center_sq3129
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3129.1
  jac_ok := checks3129.2.1
  accepted := checks3129.2.2

def tau3130 : RatBall :=
  ⟨⟨19/128, -231/640⟩, 3/1280⟩
def center3130 : GaussianRat :=
  ⟨117328287/1000000000, -255098241/1000000000⟩
def contact3130 : RatBall := localContactBall tau3130 center3130
def work3130 : RoundedTauEval :=
  evalTau precision tau3130 contact3130 logTwoBall

theorem center_sq3130 : (center3130.re : ℝ)^2 +
    (center3130.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3130]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3130 : work3130.theta.ok = true ∧
    work3130.jac.invOK = true ∧ acceptsUnitSq work3130.out = true := by decide +kernel

def cell3130 : CellCertificate where
  tauBall := tau3130
  contactCenter := center3130
  contactBall := contact3130
  work := work3130
  center_sq := center_sq3130
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3130.1
  jac_ok := checks3130.2.1
  accepted := checks3130.2.2

def tau3131 : RatBall :=
  ⟨⟨93/640, -229/640⟩, 3/1280⟩
def center3131 : GaussianRat :=
  ⟨28657529/250000000, -252991629/1000000000⟩
def contact3131 : RatBall := localContactBall tau3131 center3131
def work3131 : RoundedTauEval :=
  evalTau precision tau3131 contact3131 logTwoBall

theorem center_sq3131 : (center3131.re : ℝ)^2 +
    (center3131.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3131]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3131 : work3131.theta.ok = true ∧
    work3131.jac.invOK = true ∧ acceptsUnitSq work3131.out = true := by decide +kernel

def cell3131 : CellCertificate where
  tauBall := tau3131
  contactCenter := center3131
  contactBall := contact3131
  work := work3131
  center_sq := center_sq3131
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3131.1
  jac_ok := checks3131.2.1
  accepted := checks3131.2.2

def tau3132 : RatBall :=
  ⟨⟨19/128, -229/640⟩, 3/1280⟩
def center3132 : GaussianRat :=
  ⟨117029769/1000000000, -63174463/250000000⟩
def contact3132 : RatBall := localContactBall tau3132 center3132
def work3132 : RoundedTauEval :=
  evalTau precision tau3132 contact3132 logTwoBall

theorem center_sq3132 : (center3132.re : ℝ)^2 +
    (center3132.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3132]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3132 : work3132.theta.ok = true ∧
    work3132.jac.invOK = true ∧ acceptsUnitSq work3132.out = true := by decide +kernel

def cell3132 : CellCertificate where
  tauBall := tau3132
  contactCenter := center3132
  contactBall := contact3132
  work := work3132
  center_sq := center_sq3132
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3132.1
  jac_ok := checks3132.2.1
  accepted := checks3132.2.2

def tau3133 : RatBall :=
  ⟨⟨97/640, -237/640⟩, 3/1280⟩
def center3133 : GaussianRat :=
  ⟨60333117/500000000, -6550423/25000000⟩
def contact3133 : RatBall := localContactBall tau3133 center3133
def work3133 : RoundedTauEval :=
  evalTau precision tau3133 contact3133 logTwoBall

theorem center_sq3133 : (center3133.re : ℝ)^2 +
    (center3133.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3133]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3133 : work3133.theta.ok = true ∧
    work3133.jac.invOK = true ∧ acceptsUnitSq work3133.out = true := by decide +kernel

def cell3133 : CellCertificate where
  tauBall := tau3133
  contactCenter := center3133
  contactBall := contact3133
  work := work3133
  center_sq := center_sq3133
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3133.1
  jac_ok := checks3133.2.1
  accepted := checks3133.2.2

def tau3134 : RatBall :=
  ⟨⟨99/640, -237/640⟩, 3/1280⟩
def center3134 : GaussianRat :=
  ⟨123079793/1000000000, -65423867/250000000⟩
def contact3134 : RatBall := localContactBall tau3134 center3134

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391


