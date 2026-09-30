-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0464_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0464_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:47:13.444459+00:00
-- url     : https://prove2.me/theorems/710c0591-0506-4b7c-9fb6-97eb0145d1b6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0464 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0464 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0464 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0464 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0464 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0464

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3712 : RatBall :=
  ⟨⟨19/128, 229/640⟩, 3/1280⟩
def center3712 : GaussianRat :=
  ⟨117029769/1000000000, 63174463/250000000⟩
def contact3712 : RatBall := localContactBall tau3712 center3712
def work3712 : RoundedTauEval :=
  evalTau precision tau3712 contact3712 logTwoBall

theorem center_sq3712 : (center3712.re : ℝ)^2 +
    (center3712.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3712]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3712 : work3712.theta.ok = true ∧
    work3712.jac.invOK = true ∧ acceptsUnitSq work3712.out = true := by decide +kernel

def cell3712 : CellCertificate where
  tauBall := tau3712
  contactCenter := center3712
  contactBall := contact3712
  work := work3712
  center_sq := center_sq3712
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3712.1
  jac_ok := checks3712.2.1
  accepted := checks3712.2.2

def tau3713 : RatBall :=
  ⟨⟨93/640, 231/640⟩, 3/1280⟩
def center3713 : GaussianRat :=
  ⟨114923139/1000000000, 12769801/50000000⟩
def contact3713 : RatBall := localContactBall tau3713 center3713
def work3713 : RoundedTauEval :=
  evalTau precision tau3713 contact3713 logTwoBall

theorem center_sq3713 : (center3713.re : ℝ)^2 +
    (center3713.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3713]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3713 : work3713.theta.ok = true ∧
    work3713.jac.invOK = true ∧ acceptsUnitSq work3713.out = true := by decide +kernel

def cell3713 : CellCertificate where
  tauBall := tau3713
  contactCenter := center3713
  contactBall := contact3713
  work := work3713
  center_sq := center_sq3713
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3713.1
  jac_ok := checks3713.2.1
  accepted := checks3713.2.2

def tau3714 : RatBall :=
  ⟨⟨19/128, 231/640⟩, 3/1280⟩
def center3714 : GaussianRat :=
  ⟨117328287/1000000000, 255098241/1000000000⟩
def contact3714 : RatBall := localContactBall tau3714 center3714
def work3714 : RoundedTauEval :=
  evalTau precision tau3714 contact3714 logTwoBall

theorem center_sq3714 : (center3714.re : ℝ)^2 +
    (center3714.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3714]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3714 : work3714.theta.ok = true ∧
    work3714.jac.invOK = true ∧ acceptsUnitSq work3714.out = true := by decide +kernel

def cell3714 : CellCertificate where
  tauBall := tau3714
  contactCenter := center3714
  contactBall := contact3714
  work := work3714
  center_sq := center_sq3714
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3714.1
  jac_ok := checks3714.2.1
  accepted := checks3714.2.2

def tau3715 : RatBall :=
  ⟨⟨81/640, 233/640⟩, 3/1280⟩
def center3715 : GaussianRat :=
  ⟨12584197/125000000, 1013661/3906250⟩
def contact3715 : RatBall := localContactBall tau3715 center3715
def work3715 : RoundedTauEval :=
  evalTau precision tau3715 contact3715 logTwoBall

theorem center_sq3715 : (center3715.re : ℝ)^2 +
    (center3715.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3715]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3715 : work3715.theta.ok = true ∧
    work3715.jac.invOK = true ∧ acceptsUnitSq work3715.out = true := by decide +kernel

def cell3715 : CellCertificate where
  tauBall := tau3715
  contactCenter := center3715
  contactBall := contact3715
  work := work3715
  center_sq := center_sq3715
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3715.1
  jac_ok := checks3715.2.1
  accepted := checks3715.2.2

def tau3716 : RatBall :=
  ⟨⟨83/640, 233/640⟩, 3/1280⟩
def center3716 : GaussianRat :=
  ⟨103107441/1000000000, 129614913/500000000⟩
def contact3716 : RatBall := localContactBall tau3716 center3716
def work3716 : RoundedTauEval :=
  evalTau precision tau3716 contact3716 logTwoBall

theorem center_sq3716 : (center3716.re : ℝ)^2 +
    (center3716.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3716]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3716 : work3716.theta.ok = true ∧
    work3716.jac.invOK = true ∧ acceptsUnitSq work3716.out = true := by decide +kernel

def cell3716 : CellCertificate where
  tauBall := tau3716
  contactCenter := center3716
  contactBall := contact3716
  work := work3716
  center_sq := center_sq3716
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3716.1
  jac_ok := checks3716.2.1
  accepted := checks3716.2.2

def tau3717 : RatBall :=
  ⟨⟨81/640, 47/128⟩, 3/1280⟩
def center3717 : GaussianRat :=
  ⟨100939831/1000000000, 261935857/1000000000⟩
def contact3717 : RatBall := localContactBall tau3717 center3717
def work3717 : RoundedTauEval :=
  evalTau precision tau3717 contact3717 logTwoBall

theorem center_sq3717 : (center3717.re : ℝ)^2 +
    (center3717.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3717]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3717 : work3717.theta.ok = true ∧
    work3717.jac.invOK = true ∧ acceptsUnitSq work3717.out = true := by decide +kernel

def cell3717 : CellCertificate where
  tauBall := tau3717
  contactCenter := center3717
  contactBall := contact3717
  work := work3717
  center_sq := center_sq3717
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3717.1
  jac_ok := checks3717.2.1
  accepted := checks3717.2.2

def tau3718 : RatBall :=
  ⟨⟨83/640, 47/128⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0464


