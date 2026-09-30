-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0394_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0394_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:10:36.870961+00:00
-- url     : https://prove2.me/theorems/9a5275f4-e16e-4bdd-ab9b-2f094de92c7c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0394 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3152 : RatBall :=
  ⟨⟨101/640, -229/640⟩, 3/1280⟩
def center3152 : GaussianRat :=
  ⟨62102193/500000000, -7868253/31250000⟩
def contact3152 : RatBall := localContactBall tau3152 center3152
def work3152 : RoundedTauEval :=
  evalTau precision tau3152 contact3152 logTwoBall

theorem center_sq3152 : (center3152.re : ℝ)^2 +
    (center3152.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3152]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3152 : work3152.theta.ok = true ∧
    work3152.jac.invOK = true ∧ acceptsUnitSq work3152.out = true := by decide +kernel

def cell3152 : CellCertificate where
  tauBall := tau3152
  contactCenter := center3152
  contactBall := contact3152
  work := work3152
  center_sq := center_sq3152
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3152.1
  jac_ok := checks3152.2.1
  accepted := checks3152.2.2

def tau3153 : RatBall :=
  ⟨⟨103/640, -229/640⟩, 3/1280⟩
def center3153 : GaussianRat :=
  ⟨126587587/1000000000, -125734431/500000000⟩
def contact3153 : RatBall := localContactBall tau3153 center3153
def work3153 : RoundedTauEval :=
  evalTau precision tau3153 contact3153 logTwoBall

theorem center_sq3153 : (center3153.re : ℝ)^2 +
    (center3153.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3153]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3153 : work3153.theta.ok = true ∧
    work3153.jac.invOK = true ∧ acceptsUnitSq work3153.out = true := by decide +kernel

def cell3153 : CellCertificate where
  tauBall := tau3153
  contactCenter := center3153
  contactBall := contact3153
  work := work3153
  center_sq := center_sq3153
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3153.1
  jac_ok := checks3153.2.1
  accepted := checks3153.2.2

def tau3154 : RatBall :=
  ⟨⟨21/128, -231/640⟩, 3/1280⟩
def center3154 : GaussianRat :=
  ⟨32322943/250000000, -63381939/250000000⟩
def contact3154 : RatBall := localContactBall tau3154 center3154
def work3154 : RoundedTauEval :=
  evalTau precision tau3154 contact3154 logTwoBall

theorem center_sq3154 : (center3154.re : ℝ)^2 +
    (center3154.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3154]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3154 : work3154.theta.ok = true ∧
    work3154.jac.invOK = true ∧ acceptsUnitSq work3154.out = true := by decide +kernel

def cell3154 : CellCertificate where
  tauBall := tau3154
  contactCenter := center3154
  contactBall := contact3154
  work := work3154
  center_sq := center_sq3154
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3154.1
  jac_ok := checks3154.2.1
  accepted := checks3154.2.2

def tau3155 : RatBall :=
  ⟨⟨107/640, -231/640⟩, 3/1280⟩
def center3155 : GaussianRat :=
  ⟨65835777/500000000, -253197689/1000000000⟩
def contact3155 : RatBall := localContactBall tau3155 center3155
def work3155 : RoundedTauEval :=
  evalTau precision tau3155 contact3155 logTwoBall

theorem center_sq3155 : (center3155.re : ℝ)^2 +
    (center3155.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3155]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3155 : work3155.theta.ok = true ∧
    work3155.jac.invOK = true ∧ acceptsUnitSq work3155.out = true := by decide +kernel

def cell3155 : CellCertificate where
  tauBall := tau3155
  contactCenter := center3155
  contactBall := contact3155
  work := work3155
  center_sq := center_sq3155
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3155.1
  jac_ok := checks3155.2.1
  accepted := checks3155.2.2

def tau3156 : RatBall :=
  ⟨⟨21/128, -229/640⟩, 3/1280⟩
def center3156 : GaussianRat :=
  ⟨128966511/1000000000, -50229677/200000000⟩
def contact3156 : RatBall := localContactBall tau3156 center3156
def work3156 : RoundedTauEval :=
  evalTau precision tau3156 contact3156 logTwoBall

theorem center_sq3156 : (center3156.re : ℝ)^2 +
    (center3156.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3156]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394


