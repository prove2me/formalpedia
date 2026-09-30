-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0386
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0386
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:03:52.268999+00:00
-- url     : https://prove2.me/theorems/e40f5e88-1ac5-4735-8881-6779cbcefcc2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0386.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0386_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3092 : RoundedTauEval :=
  evalTau precision tau3092 contact3092 logTwoBall

theorem center_sq3092 : (center3092.re : ℝ)^2 +
    (center3092.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3092]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3092 : work3092.theta.ok = true ∧
    work3092.jac.invOK = true ∧ acceptsUnitSq work3092.out = true := by decide +kernel

def cell3092 : CellCertificate where
  tauBall := tau3092
  contactCenter := center3092
  contactBall := contact3092
  work := work3092
  center_sq := center_sq3092
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3092.1
  jac_ok := checks3092.2.1
  accepted := checks3092.2.2

def tau3093 : RatBall :=
  ⟨⟨77/640, -239/640⟩, 3/1280⟩
def center3093 : GaussianRat :=
  ⟨96568507/1000000000, -66842431/250000000⟩
def contact3093 : RatBall := localContactBall tau3093 center3093
def work3093 : RoundedTauEval :=
  evalTau precision tau3093 contact3093 logTwoBall

theorem center_sq3093 : (center3093.re : ℝ)^2 +
    (center3093.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3093]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3093 : work3093.theta.ok = true ∧
    work3093.jac.invOK = true ∧ acceptsUnitSq work3093.out = true := by decide +kernel

def cell3093 : CellCertificate where
  tauBall := tau3093
  contactCenter := center3093
  contactBall := contact3093
  work := work3093
  center_sq := center_sq3093
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3093.1
  jac_ok := checks3093.2.1
  accepted := checks3093.2.2

def tau3094 : RatBall :=
  ⟨⟨79/640, -239/640⟩, 3/1280⟩
def center3094 : GaussianRat :=
  ⟨99027743/1000000000, -267103523/1000000000⟩
def contact3094 : RatBall := localContactBall tau3094 center3094
def work3094 : RoundedTauEval :=
  evalTau precision tau3094 contact3094 logTwoBall

theorem center_sq3094 : (center3094.re : ℝ)^2 +
    (center3094.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3094]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3094 : work3094.theta.ok = true ∧
    work3094.jac.invOK = true ∧ acceptsUnitSq work3094.out = true := by decide +kernel

def cell3094 : CellCertificate where
  tauBall := tau3094
  contactCenter := center3094
  contactBall := contact3094
  work := work3094
  center_sq := center_sq3094
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3094.1
  jac_ok := checks3094.2.1
  accepted := checks3094.2.2

def tau3095 : RatBall :=
  ⟨⟨77/640, -237/640⟩, 3/1280⟩
def center3095 : GaussianRat :=
  ⟨96307191/1000000000, -264911783/1000000000⟩
def contact3095 : RatBall := localContactBall tau3095 center3095
def work3095 : RoundedTauEval :=
  evalTau precision tau3095 contact3095 logTwoBall

theorem center_sq3095 : (center3095.re : ℝ)^2 +
    (center3095.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3095]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3095 : work3095.theta.ok = true ∧
    work3095.jac.invOK = true ∧ acceptsUnitSq work3095.out = true := by decide +kernel

def cell3095 : CellCertificate where
  tauBall := tau3095
  contactCenter := center3095
  contactBall := contact3095
  work := work3095
  center_sq := center_sq3095
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3095.1
  jac_ok := checks3095.2.1
  accepted := checks3095.2.2

def cells : List CellCertificate := [cell3088, cell3089, cell3090, cell3091, cell3092, cell3093, cell3094, cell3095]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386


