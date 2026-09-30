-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0384
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0384
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:23:07.31077+00:00
-- url     : https://prove2.me/theorems/db096d05-e86b-4e1b-9ceb-bc15de3092fb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0384.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0384_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3076 : RoundedTauEval :=
  evalTau precision tau3076 contact3076 logTwoBall

theorem center_sq3076 : (center3076.re : ℝ)^2 +
    (center3076.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3076]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3076 : work3076.theta.ok = true ∧
    work3076.jac.invOK = true ∧ acceptsUnitSq work3076.out = true := by decide +kernel

def cell3076 : CellCertificate where
  tauBall := tau3076
  contactCenter := center3076
  contactBall := contact3076
  work := work3076
  center_sq := center_sq3076
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3076.1
  jac_ok := checks3076.2.1
  accepted := checks3076.2.2

def tau3077 : RatBall :=
  ⟨⟨83/640, -241/640⟩, 3/1280⟩
def center3077 : GaussianRat :=
  ⟨104218637/1000000000, -134502819/500000000⟩
def contact3077 : RatBall := localContactBall tau3077 center3077
def work3077 : RoundedTauEval :=
  evalTau precision tau3077 contact3077 logTwoBall

theorem center_sq3077 : (center3077.re : ℝ)^2 +
    (center3077.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3077]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3077 : work3077.theta.ok = true ∧
    work3077.jac.invOK = true ∧ acceptsUnitSq work3077.out = true := by decide +kernel

def cell3077 : CellCertificate where
  tauBall := tau3077
  contactCenter := center3077
  contactBall := contact3077
  work := work3077
  center_sq := center_sq3077
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3077.1
  jac_ok := checks3077.2.1
  accepted := checks3077.2.2

def tau3078 : RatBall :=
  ⟨⟨17/128, -241/640⟩, 3/1280⟩
def center3078 : GaussianRat :=
  ⟨53336381/500000000, -268717167/1000000000⟩
def contact3078 : RatBall := localContactBall tau3078 center3078
def work3078 : RoundedTauEval :=
  evalTau precision tau3078 contact3078 logTwoBall

theorem center_sq3078 : (center3078.re : ℝ)^2 +
    (center3078.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3078]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3078 : work3078.theta.ok = true ∧
    work3078.jac.invOK = true ∧ acceptsUnitSq work3078.out = true := by decide +kernel

def cell3078 : CellCertificate where
  tauBall := tau3078
  contactCenter := center3078
  contactBall := contact3078
  work := work3078
  center_sq := center_sq3078
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3078.1
  jac_ok := checks3078.2.1
  accepted := checks3078.2.2

def tau3079 : RatBall :=
  ⟨⟨87/640, -241/640⟩, 3/1280⟩
def center3079 : GaussianRat :=
  ⟨109122947/1000000000, -53684517/200000000⟩
def contact3079 : RatBall := localContactBall tau3079 center3079
def work3079 : RoundedTauEval :=
  evalTau precision tau3079 contact3079 logTwoBall

theorem center_sq3079 : (center3079.re : ℝ)^2 +
    (center3079.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3079]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3079 : work3079.theta.ok = true ∧
    work3079.jac.invOK = true ∧ acceptsUnitSq work3079.out = true := by decide +kernel

def cell3079 : CellCertificate where
  tauBall := tau3079
  contactCenter := center3079
  contactBall := contact3079
  work := work3079
  center_sq := center_sq3079
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3079.1
  jac_ok := checks3079.2.1
  accepted := checks3079.2.2

def cells : List CellCertificate := [cell3072, cell3073, cell3074, cell3075, cell3076, cell3077, cell3078, cell3079]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384


