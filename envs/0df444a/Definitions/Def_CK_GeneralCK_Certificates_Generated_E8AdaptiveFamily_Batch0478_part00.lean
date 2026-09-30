-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0478_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0478_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:33:40.590767+00:00
-- url     : https://prove2.me/theorems/a2029994-f6f6-48d0-b960-fdee7aeac9c1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0478 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3824 : RatBall :=
  ⟨⟨113/640, 231/640⟩, 3/1280⟩
def center3824 : GaussianRat :=
  ⟨138783923/1000000000, 252176463/1000000000⟩
def contact3824 : RatBall := localContactBall tau3824 center3824
def work3824 : RoundedTauEval :=
  evalTau precision tau3824 contact3824 logTwoBall

theorem center_sq3824 : (center3824.re : ℝ)^2 +
    (center3824.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3824]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3824 : work3824.theta.ok = true ∧
    work3824.jac.invOK = true ∧ acceptsUnitSq work3824.out = true := by decide +kernel

def cell3824 : CellCertificate where
  tauBall := tau3824
  contactCenter := center3824
  contactBall := contact3824
  work := work3824
  center_sq := center_sq3824
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3824.1
  jac_ok := checks3824.2.1
  accepted := checks3824.2.2

def tau3825 : RatBall :=
  ⟨⟨117/640, 229/640⟩, 3/1280⟩
def center3825 : GaussianRat :=
  ⟨143146729/1000000000, 249118251/1000000000⟩
def contact3825 : RatBall := localContactBall tau3825 center3825
def work3825 : RoundedTauEval :=
  evalTau precision tau3825 contact3825 logTwoBall

theorem center_sq3825 : (center3825.re : ℝ)^2 +
    (center3825.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3825]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3825 : work3825.theta.ok = true ∧
    work3825.jac.invOK = true ∧ acceptsUnitSq work3825.out = true := by decide +kernel

def cell3825 : CellCertificate where
  tauBall := tau3825
  contactCenter := center3825
  contactBall := contact3825
  work := work3825
  center_sq := center_sq3825
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3825.1
  jac_ok := checks3825.2.1
  accepted := checks3825.2.2

def tau3826 : RatBall :=
  ⟨⟨121/640, 45/128⟩, 3/1280⟩
def center3826 : GaussianRat :=
  ⟨36780017/250000000, 243731207/1000000000⟩
def contact3826 : RatBall := localContactBall tau3826 center3826
def work3826 : RoundedTauEval :=
  evalTau precision tau3826 contact3826 logTwoBall

theorem center_sq3826 : (center3826.re : ℝ)^2 +
    (center3826.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3826]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3826 : work3826.theta.ok = true ∧
    work3826.jac.invOK = true ∧ acceptsUnitSq work3826.out = true := by decide +kernel

def cell3826 : CellCertificate where
  tauBall := tau3826
  contactCenter := center3826
  contactBall := contact3826
  work := work3826
  center_sq := center_sq3826
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3826.1
  jac_ok := checks3826.2.1
  accepted := checks3826.2.2

def tau3827 : RatBall :=
  ⟨⟨123/640, 45/128⟩, 3/1280⟩
def center3827 : GaussianRat :=
  ⟨149448351/1000000000, 9735017/40000000⟩
def contact3827 : RatBall := localContactBall tau3827 center3827
def work3827 : RoundedTauEval :=
  evalTau precision tau3827 contact3827 logTwoBall

theorem center_sq3827 : (center3827.re : ℝ)^2 +
    (center3827.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3827]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3827 : work3827.theta.ok = true ∧
    work3827.jac.invOK = true ∧ acceptsUnitSq work3827.out = true := by decide +kernel

def cell3827 : CellCertificate where
  tauBall := tau3827
  contactCenter := center3827
  contactBall := contact3827
  work := work3827
  center_sq := center_sq3827
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3827.1
  jac_ok := checks3827.2.1
  accepted := checks3827.2.2

def tau3828 : RatBall :=
  ⟨⟨121/640, 227/640⟩, 3/1280⟩
def center3828 : GaussianRat :=
  ⟨147475889/1000000000, 123032099/500000000⟩
def contact3828 : RatBall := localContactBall tau3828 center3828
def work3828 : RoundedTauEval :=
  evalTau precision tau3828 contact3828 logTwoBall

theorem center_sq3828 : (center3828.re : ℝ)^2 +
    (center3828.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3828]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3828 : work3828.theta.ok = true ∧
    work3828.jac.invOK = true ∧ acceptsUnitSq work3828.out = true := by decide +kernel

def cell3828 : CellCertificate where
  tauBall := tau3828
  contactCenter := center3828
  contactBall := contact3828
  work := work3828
  center_sq := center_sq3828
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3828.1
  jac_ok := checks3828.2.1
  accepted := checks3828.2.2

def tau3829 : RatBall :=
  ⟨⟨141/640, 213/640⟩, 3/1280⟩
def center3829 : GaussianRat :=
  ⟨33577827/200000000, 28294879/125000000⟩
def contact3829 : RatBall := localContactBall tau3829 center3829
def work3829 : RoundedTauEval :=
  evalTau precision tau3829 contact3829 logTwoBall

theorem center_sq3829 : (center3829.re : ℝ)^2 +
    (center3829.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3829]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3829 : work3829.theta.ok = true ∧
    work3829.jac.invOK = true ∧ acceptsUnitSq work3829.out = true := by decide +kernel

def cell3829 : CellCertificate where
  tauBall := tau3829
  contactCenter := center3829
  contactBall := contact3829
  work := work3829
  center_sq := center_sq3829
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3829.1
  jac_ok := checks3829.2.1
  accepted := checks3829.2.2

def tau3830 : RatBall :=
  ⟨⟨143/640, 213/640⟩, 3/1280⟩
def center3830 : GaussianRat :=
  ⟨85071813/500000000, 28248739/125000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478


