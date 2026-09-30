-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0457_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0457_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:50:09.333343+00:00
-- url     : https://prove2.me/theorems/c50e6310-4dc1-480c-93ec-9c6aaf128b32
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0457 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0457 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0457 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0457 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0457 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0457

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3656 : RatBall :=
  ⟨⟨11/128, 49/128⟩, 3/1280⟩
def center3656 : GaussianRat :=
  ⟨69887307/1000000000, 277394317/1000000000⟩
def contact3656 : RatBall := localContactBall tau3656 center3656
def work3656 : RoundedTauEval :=
  evalTau precision tau3656 contact3656 logTwoBall

theorem center_sq3656 : (center3656.re : ℝ)^2 +
    (center3656.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3656]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3656 : work3656.theta.ok = true ∧
    work3656.jac.invOK = true ∧ acceptsUnitSq work3656.out = true := by decide +kernel

def cell3656 : CellCertificate where
  tauBall := tau3656
  contactCenter := center3656
  contactBall := contact3656
  work := work3656
  center_sq := center_sq3656
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3656.1
  jac_ok := checks3656.2.1
  accepted := checks3656.2.2

def tau3657 : RatBall :=
  ⟨⟨53/640, 247/640⟩, 3/1280⟩
def center3657 : GaussianRat :=
  ⟨33782393/500000000, 56022603/200000000⟩
def contact3657 : RatBall := localContactBall tau3657 center3657
def work3657 : RoundedTauEval :=
  evalTau precision tau3657 contact3657 logTwoBall

theorem center_sq3657 : (center3657.re : ℝ)^2 +
    (center3657.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3657]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3657 : work3657.theta.ok = true ∧
    work3657.jac.invOK = true ∧ acceptsUnitSq work3657.out = true := by decide +kernel

def cell3657 : CellCertificate where
  tauBall := tau3657
  contactCenter := center3657
  contactBall := contact3657
  work := work3657
  center_sq := center_sq3657
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3657.1
  jac_ok := checks3657.2.1
  accepted := checks3657.2.2

def tau3658 : RatBall :=
  ⟨⟨11/128, 247/640⟩, 3/1280⟩
def center3658 : GaussianRat :=
  ⟨70088901/1000000000, 139956777/500000000⟩
def contact3658 : RatBall := localContactBall tau3658 center3658
def work3658 : RoundedTauEval :=
  evalTau precision tau3658 contact3658 logTwoBall

theorem center_sq3658 : (center3658.re : ℝ)^2 +
    (center3658.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3658]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3658 : work3658.theta.ok = true ∧
    work3658.jac.invOK = true ∧ acceptsUnitSq work3658.out = true := by decide +kernel

def cell3658 : CellCertificate where
  tauBall := tau3658
  contactCenter := center3658
  contactBall := contact3658
  work := work3658
  center_sq := center_sq3658
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3658.1
  jac_ok := checks3658.2.1
  accepted := checks3658.2.2

def tau3659 : RatBall :=
  ⟨⟨57/640, 241/640⟩, 3/1280⟩
def center3659 : GaussianRat :=
  ⟨1439861/20000000, 68044601/250000000⟩
def contact3659 : RatBall := localContactBall tau3659 center3659
def work3659 : RoundedTauEval :=
  evalTau precision tau3659 contact3659 logTwoBall

theorem center_sq3659 : (center3659.re : ℝ)^2 +
    (center3659.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3659]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3659 : work3659.theta.ok = true ∧
    work3659.jac.invOK = true ∧ acceptsUnitSq work3659.out = true := by decide +kernel

def cell3659 : CellCertificate where
  tauBall := tau3659
  contactCenter := center3659
  contactBall := contact3659
  work := work3659
  center_sq := center_sq3659
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3659.1
  jac_ok := checks3659.2.1
  accepted := checks3659.2.2

def tau3660 : RatBall :=
  ⟨⟨59/640, 241/640⟩, 3/1280⟩
def center3660 : GaussianRat :=
  ⟨37245497/500000000, 8499173/31250000⟩
def contact3660 : RatBall := localContactBall tau3660 center3660
def work3660 : RoundedTauEval :=
  evalTau precision tau3660 contact3660 logTwoBall

theorem center_sq3660 : (center3660.re : ℝ)^2 +
    (center3660.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3660]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3660 : work3660.theta.ok = true ∧
    work3660.jac.invOK = true ∧ acceptsUnitSq work3660.out = true := by decide +kernel

def cell3660 : CellCertificate where
  tauBall := tau3660
  contactCenter := center3660
  contactBall := contact3660
  work := work3660
  center_sq := center_sq3660
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3660.1
  jac_ok := checks3660.2.1
  accepted := checks3660.2.2

def tau3661 : RatBall :=
  ⟨⟨57/640, 243/640⟩, 3/1280⟩
def center3661 : GaussianRat :=
  ⟨72195957/1000000000, 1716757/6250000⟩
def contact3661 : RatBall := localContactBall tau3661 center3661
def work3661 : RoundedTauEval :=
  evalTau precision tau3661 contact3661 logTwoBall

theorem center_sq3661 : (center3661.re : ℝ)^2 +
    (center3661.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3661]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3661 : work3661.theta.ok = true ∧
    work3661.jac.invOK = true ∧ acceptsUnitSq work3661.out = true := by decide +kernel

def cell3661 : CellCertificate where
  tauBall := tau3661
  contactCenter := center3661
  contactBall := contact3661
  work := work3661
  center_sq := center_sq3661
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3661.1
  jac_ok := checks3661.2.1
  accepted := checks3661.2.2

def tau3662 : RatBall :=
  ⟨⟨59/640, 243/640⟩, 3/1280⟩
def center3662 : GaussianRat :=
  ⟨74700643/1000000000, 13723671/50000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0457


