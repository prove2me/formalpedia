-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0379
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0379
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:59:40.422076+00:00
-- url     : https://prove2.me/theorems/ccb80a05-e099-48fd-a187-fef12086ca38
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0379.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0379_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3036 : (center3036.re : ℝ)^2 +
    (center3036.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3036]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3036 : work3036.theta.ok = true ∧
    work3036.jac.invOK = true ∧ acceptsUnitSq work3036.out = true := by decide +kernel

def cell3036 : CellCertificate where
  tauBall := tau3036
  contactCenter := center3036
  contactBall := contact3036
  work := work3036
  center_sq := center_sq3036
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3036.1
  jac_ok := checks3036.2.1
  accepted := checks3036.2.2

def tau3037 : RatBall :=
  ⟨⟨61/640, -49/128⟩, 3/1280⟩
def center3037 : GaussianRat :=
  ⟨3096871/40000000, -138381321/500000000⟩
def contact3037 : RatBall := localContactBall tau3037 center3037
def work3037 : RoundedTauEval :=
  evalTau precision tau3037 contact3037 logTwoBall

theorem center_sq3037 : (center3037.re : ℝ)^2 +
    (center3037.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3037]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3037 : work3037.theta.ok = true ∧
    work3037.jac.invOK = true ∧ acceptsUnitSq work3037.out = true := by decide +kernel

def cell3037 : CellCertificate where
  tauBall := tau3037
  contactCenter := center3037
  contactBall := contact3037
  work := work3037
  center_sq := center_sq3037
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3037.1
  jac_ok := checks3037.2.1
  accepted := checks3037.2.2

def tau3038 : RatBall :=
  ⟨⟨63/640, -49/128⟩, 3/1280⟩
def center3038 : GaussianRat :=
  ⟨39963667/500000000, -276538391/1000000000⟩
def contact3038 : RatBall := localContactBall tau3038 center3038
def work3038 : RoundedTauEval :=
  evalTau precision tau3038 contact3038 logTwoBall

theorem center_sq3038 : (center3038.re : ℝ)^2 +
    (center3038.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3038]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3038 : work3038.theta.ok = true ∧
    work3038.jac.invOK = true ∧ acceptsUnitSq work3038.out = true := by decide +kernel

def cell3038 : CellCertificate where
  tauBall := tau3038
  contactCenter := center3038
  contactBall := contact3038
  work := work3038
  center_sq := center_sq3038
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3038.1
  jac_ok := checks3038.2.1
  accepted := checks3038.2.2

def tau3039 : RatBall :=
  ⟨⟨57/640, -243/640⟩, 3/1280⟩
def center3039 : GaussianRat :=
  ⟨72195957/1000000000, -1716757/6250000⟩
def contact3039 : RatBall := localContactBall tau3039 center3039
def work3039 : RoundedTauEval :=
  evalTau precision tau3039 contact3039 logTwoBall

theorem center_sq3039 : (center3039.re : ℝ)^2 +
    (center3039.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3039]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3039 : work3039.theta.ok = true ∧
    work3039.jac.invOK = true ∧ acceptsUnitSq work3039.out = true := by decide +kernel

def cell3039 : CellCertificate where
  tauBall := tau3039
  contactCenter := center3039
  contactBall := contact3039
  work := work3039
  center_sq := center_sq3039
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3039.1
  jac_ok := checks3039.2.1
  accepted := checks3039.2.2

def cells : List CellCertificate := [cell3032, cell3033, cell3034, cell3035, cell3036, cell3037, cell3038, cell3039]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379


