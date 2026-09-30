-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0389
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0389
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:51:22.842285+00:00
-- url     : https://prove2.me/theorems/56d3f35e-b228-47f0-8f1a-85060a704bc6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0389.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0389_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3116 : RoundedTauEval :=
  evalTau precision tau3116 contact3116 logTwoBall

theorem center_sq3116 : (center3116.re : ℝ)^2 +
    (center3116.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3116]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3116 : work3116.theta.ok = true ∧
    work3116.jac.invOK = true ∧ acceptsUnitSq work3116.out = true := by decide +kernel

def cell3116 : CellCertificate where
  tauBall := tau3116
  contactCenter := center3116
  contactBall := contact3116
  work := work3116
  center_sq := center_sq3116
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3116.1
  jac_ok := checks3116.2.1
  accepted := checks3116.2.2

def tau3117 : RatBall :=
  ⟨⟨93/640, -239/640⟩, 3/1280⟩
def center3117 : GaussianRat :=
  ⟨116135629/1000000000, -265069807/1000000000⟩
def contact3117 : RatBall := localContactBall tau3117 center3117
def work3117 : RoundedTauEval :=
  evalTau precision tau3117 contact3117 logTwoBall

theorem center_sq3117 : (center3117.re : ℝ)^2 +
    (center3117.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3117]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3117 : work3117.theta.ok = true ∧
    work3117.jac.invOK = true ∧ acceptsUnitSq work3117.out = true := by decide +kernel

def cell3117 : CellCertificate where
  tauBall := tau3117
  contactCenter := center3117
  contactBall := contact3117
  work := work3117
  center_sq := center_sq3117
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3117.1
  jac_ok := checks3117.2.1
  accepted := checks3117.2.2

def tau3118 : RatBall :=
  ⟨⟨19/128, -239/640⟩, 3/1280⟩
def center3118 : GaussianRat :=
  ⟨118563451/1000000000, -66188883/250000000⟩
def contact3118 : RatBall := localContactBall tau3118 center3118
def work3118 : RoundedTauEval :=
  evalTau precision tau3118 contact3118 logTwoBall

theorem center_sq3118 : (center3118.re : ℝ)^2 +
    (center3118.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3118]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3118 : work3118.theta.ok = true ∧
    work3118.jac.invOK = true ∧ acceptsUnitSq work3118.out = true := by decide +kernel

def cell3118 : CellCertificate where
  tauBall := tau3118
  contactCenter := center3118
  contactBall := contact3118
  work := work3118
  center_sq := center_sq3118
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3118.1
  jac_ok := checks3118.2.1
  accepted := checks3118.2.2

def tau3119 : RatBall :=
  ⟨⟨93/640, -237/640⟩, 3/1280⟩
def center3119 : GaussianRat :=
  ⟨115826349/1000000000, -52528557/200000000⟩
def contact3119 : RatBall := localContactBall tau3119 center3119
def work3119 : RoundedTauEval :=
  evalTau precision tau3119 contact3119 logTwoBall

theorem center_sq3119 : (center3119.re : ℝ)^2 +
    (center3119.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3119]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3119 : work3119.theta.ok = true ∧
    work3119.jac.invOK = true ∧ acceptsUnitSq work3119.out = true := by decide +kernel

def cell3119 : CellCertificate where
  tauBall := tau3119
  contactCenter := center3119
  contactBall := contact3119
  work := work3119
  center_sq := center_sq3119
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3119.1
  jac_ok := checks3119.2.1
  accepted := checks3119.2.2

def cells : List CellCertificate := [cell3112, cell3113, cell3114, cell3115, cell3116, cell3117, cell3118, cell3119]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389


