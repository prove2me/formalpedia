-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0430
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0430
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:27:00.693508+00:00
-- url     : https://prove2.me/theorems/7a48f3ee-81ca-41e4-90d9-61343103222f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0430.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0430_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3444 : RoundedTauEval :=
  evalTau precision tau3444 contact3444 logTwoBall

theorem center_sq3444 : (center3444.re : ℝ)^2 +
    (center3444.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3444]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3444 : work3444.theta.ok = true ∧
    work3444.jac.invOK = true ∧ acceptsUnitSq work3444.out = true := by decide +kernel

def cell3444 : CellCertificate where
  tauBall := tau3444
  contactCenter := center3444
  contactBall := contact3444
  work := work3444
  center_sq := center_sq3444
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3444.1
  jac_ok := checks3444.2.1
  accepted := checks3444.2.2

def tau3445 : RatBall :=
  ⟨⟨-37/640, 253/640⟩, 3/1280⟩
def center3445 : GaussianRat :=
  ⟨-47706761/1000000000, 36139591/125000000⟩
def contact3445 : RatBall := localContactBall tau3445 center3445
def work3445 : RoundedTauEval :=
  evalTau precision tau3445 contact3445 logTwoBall

theorem center_sq3445 : (center3445.re : ℝ)^2 +
    (center3445.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3445]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3445 : work3445.theta.ok = true ∧
    work3445.jac.invOK = true ∧ acceptsUnitSq work3445.out = true := by decide +kernel

def cell3445 : CellCertificate where
  tauBall := tau3445
  contactCenter := center3445
  contactBall := contact3445
  work := work3445
  center_sq := center_sq3445
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3445.1
  jac_ok := checks3445.2.1
  accepted := checks3445.2.2

def tau3446 : RatBall :=
  ⟨⟨-7/128, 253/640⟩, 3/1280⟩
def center3446 : GaussianRat :=
  ⟨-9027887/200000000, 289257137/1000000000⟩
def contact3446 : RatBall := localContactBall tau3446 center3446
def work3446 : RoundedTauEval :=
  evalTau precision tau3446 contact3446 logTwoBall

theorem center_sq3446 : (center3446.re : ℝ)^2 +
    (center3446.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3446]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3446 : work3446.theta.ok = true ∧
    work3446.jac.invOK = true ∧ acceptsUnitSq work3446.out = true := by decide +kernel

def cell3446 : CellCertificate where
  tauBall := tau3446
  contactCenter := center3446
  contactBall := contact3446
  work := work3446
  center_sq := center_sq3446
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3446.1
  jac_ok := checks3446.2.1
  accepted := checks3446.2.2

def tau3447 : RatBall :=
  ⟨⟨-33/640, 253/640⟩, 3/1280⟩
def center3447 : GaussianRat :=
  ⟨-42570217/1000000000, 144694949/500000000⟩
def contact3447 : RatBall := localContactBall tau3447 center3447
def work3447 : RoundedTauEval :=
  evalTau precision tau3447 contact3447 logTwoBall

theorem center_sq3447 : (center3447.re : ℝ)^2 +
    (center3447.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3447]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3447 : work3447.theta.ok = true ∧
    work3447.jac.invOK = true ∧ acceptsUnitSq work3447.out = true := by decide +kernel

def cell3447 : CellCertificate where
  tauBall := tau3447
  contactCenter := center3447
  contactBall := contact3447
  work := work3447
  center_sq := center_sq3447
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3447.1
  jac_ok := checks3447.2.1
  accepted := checks3447.2.2

def cells : List CellCertificate := [cell3440, cell3441, cell3442, cell3443, cell3444, cell3445, cell3446, cell3447]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430


