-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0455_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0455_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:20:04.694339+00:00
-- url     : https://prove2.me/theorems/c5861300-6b14-4ccc-8c85-e5161df4c7d8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0455 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0455 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0455 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0455 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0455 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0455

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3640 : RatBall :=
  ⟨⟨41/640, 253/640⟩, 3/1280⟩
def center3640 : GaussianRat :=
  ⟨52835321/1000000000, 11552523/40000000⟩
def contact3640 : RatBall := localContactBall tau3640 center3640
def work3640 : RoundedTauEval :=
  evalTau precision tau3640 contact3640 logTwoBall

theorem center_sq3640 : (center3640.re : ℝ)^2 +
    (center3640.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3640]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3640 : work3640.theta.ok = true ∧
    work3640.jac.invOK = true ∧ acceptsUnitSq work3640.out = true := by decide +kernel

def cell3640 : CellCertificate where
  tauBall := tau3640
  contactCenter := center3640
  contactBall := contact3640
  work := work3640
  center_sq := center_sq3640
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3640.1
  jac_ok := checks3640.2.1
  accepted := checks3640.2.2

def tau3641 : RatBall :=
  ⟨⟨43/640, 253/640⟩, 3/1280⟩
def center3641 : GaussianRat :=
  ⟨55396349/1000000000, 28864989/100000000⟩
def contact3641 : RatBall := localContactBall tau3641 center3641
def work3641 : RoundedTauEval :=
  evalTau precision tau3641 contact3641 logTwoBall

theorem center_sq3641 : (center3641.re : ℝ)^2 +
    (center3641.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3641]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3641 : work3641.theta.ok = true ∧
    work3641.jac.invOK = true ∧ acceptsUnitSq work3641.out = true := by decide +kernel

def cell3641 : CellCertificate where
  tauBall := tau3641
  contactCenter := center3641
  contactBall := contact3641
  work := work3641
  center_sq := center_sq3641
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3641.1
  jac_ok := checks3641.2.1
  accepted := checks3641.2.2

def tau3642 : RatBall :=
  ⟨⟨9/128, 253/640⟩, 3/1280⟩
def center3642 : GaussianRat :=
  ⟨5795507/100000000, 288479173/1000000000⟩
def contact3642 : RatBall := localContactBall tau3642 center3642
def work3642 : RoundedTauEval :=
  evalTau precision tau3642 contact3642 logTwoBall

theorem center_sq3642 : (center3642.re : ℝ)^2 +
    (center3642.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3642]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3642 : work3642.theta.ok = true ∧
    work3642.jac.invOK = true ∧ acceptsUnitSq work3642.out = true := by decide +kernel

def cell3642 : CellCertificate where
  tauBall := tau3642
  contactCenter := center3642
  contactBall := contact3642
  work := work3642
  center_sq := center_sq3642
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3642.1
  jac_ok := checks3642.2.1
  accepted := checks3642.2.2

def tau3643 : RatBall :=
  ⟨⟨49/640, 241/640⟩, 3/1280⟩
def center3643 : GaussianRat :=
  ⟨12394897/200000000, 272930361/1000000000⟩
def contact3643 : RatBall := localContactBall tau3643 center3643
def work3643 : RoundedTauEval :=
  evalTau precision tau3643 contact3643 logTwoBall

theorem center_sq3643 : (center3643.re : ℝ)^2 +
    (center3643.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3643]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3643 : work3643.theta.ok = true ∧
    work3643.jac.invOK = true ∧ acceptsUnitSq work3643.out = true := by decide +kernel

def cell3643 : CellCertificate where
  tauBall := tau3643
  contactCenter := center3643
  contactBall := contact3643
  work := work3643
  center_sq := center_sq3643
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3643.1
  jac_ok := checks3643.2.1
  accepted := checks3643.2.2

def tau3644 : RatBall :=
  ⟨⟨51/640, 241/640⟩, 3/1280⟩
def center3644 : GaussianRat :=
  ⟨16120741/250000000, 34094071/125000000⟩
def contact3644 : RatBall := localContactBall tau3644 center3644
def work3644 : RoundedTauEval :=
  evalTau precision tau3644 contact3644 logTwoBall

theorem center_sq3644 : (center3644.re : ℝ)^2 +
    (center3644.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3644]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3644 : work3644.theta.ok = true ∧
    work3644.jac.invOK = true ∧ acceptsUnitSq work3644.out = true := by decide +kernel

def cell3644 : CellCertificate where
  tauBall := tau3644
  contactCenter := center3644
  contactBall := contact3644
  work := work3644
  center_sq := center_sq3644
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3644.1
  jac_ok := checks3644.2.1
  accepted := checks3644.2.2

def tau3645 : RatBall :=
  ⟨⟨49/640, 243/640⟩, 3/1280⟩
def center3645 : GaussianRat :=
  ⟨12430013/200000000, 275443499/1000000000⟩
def contact3645 : RatBall := localContactBall tau3645 center3645
def work3645 : RoundedTauEval :=
  evalTau precision tau3645 contact3645 logTwoBall

theorem center_sq3645 : (center3645.re : ℝ)^2 +
    (center3645.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3645]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3645 : work3645.theta.ok = true ∧
    work3645.jac.invOK = true ∧ acceptsUnitSq work3645.out = true := by decide +kernel

def cell3645 : CellCertificate where
  tauBall := tau3645
  contactCenter := center3645
  contactBall := contact3645
  work := work3645
  center_sq := center_sq3645
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3645.1
  jac_ok := checks3645.2.1
  accepted := checks3645.2.2

def tau3646 : RatBall :=
  ⟨⟨51/640, 243/640⟩, 3/1280⟩
def center3646 : GaussianRat :=
  ⟨32332713/500000000, 275263239/1000000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0455


