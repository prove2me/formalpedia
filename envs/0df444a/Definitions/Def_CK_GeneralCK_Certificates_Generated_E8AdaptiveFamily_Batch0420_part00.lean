-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0420_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0420_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:56:06.296277+00:00
-- url     : https://prove2.me/theorems/3ea1e91a-b305-42d5-8e2e-6973d17b05a7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0420 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3360 : RatBall :=
  ⟨⟨-13/128, 247/640⟩, 3/1280⟩
def center3360 : GaussianRat :=
  ⟨-82665793/1000000000, 278811601/1000000000⟩
def contact3360 : RatBall := localContactBall tau3360 center3360
def work3360 : RoundedTauEval :=
  evalTau precision tau3360 contact3360 logTwoBall

theorem center_sq3360 : (center3360.re : ℝ)^2 +
    (center3360.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3360]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3360 : work3360.theta.ok = true ∧
    work3360.jac.invOK = true ∧ acceptsUnitSq work3360.out = true := by decide +kernel

def cell3360 : CellCertificate where
  tauBall := tau3360
  contactCenter := center3360
  contactBall := contact3360
  work := work3360
  center_sq := center_sq3360
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3360.1
  jac_ok := checks3360.2.1
  accepted := checks3360.2.2

def tau3361 : RatBall :=
  ⟨⟨-63/640, 241/640⟩, 3/1280⟩
def center3361 : GaussianRat :=
  ⟨-15895643/200000000, 271543799/1000000000⟩
def contact3361 : RatBall := localContactBall tau3361 center3361
def work3361 : RoundedTauEval :=
  evalTau precision tau3361 contact3361 logTwoBall

theorem center_sq3361 : (center3361.re : ℝ)^2 +
    (center3361.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3361]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3361 : work3361.theta.ok = true ∧
    work3361.jac.invOK = true ∧ acceptsUnitSq work3361.out = true := by decide +kernel

def cell3361 : CellCertificate where
  tauBall := tau3361
  contactCenter := center3361
  contactBall := contact3361
  work := work3361
  center_sq := center_sq3361
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3361.1
  jac_ok := checks3361.2.1
  accepted := checks3361.2.2

def tau3362 : RatBall :=
  ⟨⟨-61/640, 241/640⟩, 3/1280⟩
def center3362 : GaussianRat :=
  ⟨-38493039/500000000, 67940497/250000000⟩
def contact3362 : RatBall := localContactBall tau3362 center3362
def work3362 : RoundedTauEval :=
  evalTau precision tau3362 contact3362 logTwoBall

theorem center_sq3362 : (center3362.re : ℝ)^2 +
    (center3362.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3362]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3362 : work3362.theta.ok = true ∧
    work3362.jac.invOK = true ∧ acceptsUnitSq work3362.out = true := by decide +kernel

def cell3362 : CellCertificate where
  tauBall := tau3362
  contactCenter := center3362
  contactBall := contact3362
  work := work3362
  center_sq := center_sq3362
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3362.1
  jac_ok := checks3362.2.1
  accepted := checks3362.2.2

def tau3363 : RatBall :=
  ⟨⟨-63/640, 243/640⟩, 3/1280⟩
def center3363 : GaussianRat :=
  ⟨-79701237/1000000000, 274037749/1000000000⟩
def contact3363 : RatBall := localContactBall tau3363 center3363
def work3363 : RoundedTauEval :=
  evalTau precision tau3363 contact3363 logTwoBall

theorem center_sq3363 : (center3363.re : ℝ)^2 +
    (center3363.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3363]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3363 : work3363.theta.ok = true ∧
    work3363.jac.invOK = true ∧ acceptsUnitSq work3363.out = true := by decide +kernel

def cell3363 : CellCertificate where
  tauBall := tau3363
  contactCenter := center3363
  contactBall := contact3363
  work := work3363
  center_sq := center_sq3363
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3363.1
  jac_ok := checks3363.2.1
  accepted := checks3363.2.2

def tau3364 : RatBall :=
  ⟨⟨-61/640, 243/640⟩, 3/1280⟩
def center3364 : GaussianRat :=
  ⟨-77202433/1000000000, 5485179/20000000⟩
def contact3364 : RatBall := localContactBall tau3364 center3364
def work3364 : RoundedTauEval :=
  evalTau precision tau3364 contact3364 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420


