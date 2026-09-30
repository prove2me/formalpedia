-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0449_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0449_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:08:48.498458+00:00
-- url     : https://prove2.me/theorems/15f2556c-3fea-4d25-bc68-a6a737ffb569
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0449 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3592 : RatBall :=
  ⟨⟨5/128, 253/640⟩, 3/1280⟩
def center3592 : GaussianRat :=
  ⟨16138267/500000000, 7246099/25000000⟩
def contact3592 : RatBall := localContactBall tau3592 center3592
def work3592 : RoundedTauEval :=
  evalTau precision tau3592 contact3592 logTwoBall

theorem center_sq3592 : (center3592.re : ℝ)^2 +
    (center3592.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3592]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3592 : work3592.theta.ok = true ∧
    work3592.jac.invOK = true ∧ acceptsUnitSq work3592.out = true := by decide +kernel

def cell3592 : CellCertificate where
  tauBall := tau3592
  contactCenter := center3592
  contactBall := contact3592
  work := work3592
  center_sq := center_sq3592
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3592.1
  jac_ok := checks3592.2.1
  accepted := checks3592.2.2

def tau3593 : RatBall :=
  ⟨⟨27/640, 253/640⟩, 3/1280⟩
def center3593 : GaussianRat :=
  ⟨6970453/200000000, 289742037/1000000000⟩
def contact3593 : RatBall := localContactBall tau3593 center3593
def work3593 : RoundedTauEval :=
  evalTau precision tau3593 contact3593 logTwoBall

theorem center_sq3593 : (center3593.re : ℝ)^2 +
    (center3593.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3593]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3593 : work3593.theta.ok = true ∧
    work3593.jac.invOK = true ∧ acceptsUnitSq work3593.out = true := by decide +kernel

def cell3593 : CellCertificate where
  tauBall := tau3593
  contactCenter := center3593
  contactBall := contact3593
  work := work3593
  center_sq := center_sq3593
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3593.1
  jac_ok := checks3593.2.1
  accepted := checks3593.2.2

def tau3594 : RatBall :=
  ⟨⟨5/128, 51/128⟩, 3/1280⟩
def center3594 : GaussianRat :=
  ⟨32375263/1000000000, 292424289/1000000000⟩
def contact3594 : RatBall := localContactBall tau3594 center3594
def work3594 : RoundedTauEval :=
  evalTau precision tau3594 contact3594 logTwoBall

theorem center_sq3594 : (center3594.re : ℝ)^2 +
    (center3594.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3594]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449


