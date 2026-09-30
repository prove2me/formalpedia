-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0429_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0429_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:18:17.895307+00:00
-- url     : https://prove2.me/theorems/4eee5123-8a61-477c-891b-9b0fa4575f77
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0429 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3432 : RatBall :=
  ⟨⟨-41/640, 251/640⟩, 3/1280⟩
def center3432 : GaussianRat :=
  ⟨-52677009/1000000000, 143127347/500000000⟩
def contact3432 : RatBall := localContactBall tau3432 center3432
def work3432 : RoundedTauEval :=
  evalTau precision tau3432 contact3432 logTwoBall

theorem center_sq3432 : (center3432.re : ℝ)^2 +
    (center3432.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3432]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3432 : work3432.theta.ok = true ∧
    work3432.jac.invOK = true ∧ acceptsUnitSq work3432.out = true := by decide +kernel

def cell3432 : CellCertificate where
  tauBall := tau3432
  contactCenter := center3432
  contactBall := contact3432
  work := work3432
  center_sq := center_sq3432
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3432.1
  jac_ok := checks3432.2.1
  accepted := checks3432.2.2

def tau3433 : RatBall :=
  ⟨⟨-9/128, 253/640⟩, 3/1280⟩
def center3433 : GaussianRat :=
  ⟨-5795507/100000000, 288479173/1000000000⟩
def contact3433 : RatBall := localContactBall tau3433 center3433
def work3433 : RoundedTauEval :=
  evalTau precision tau3433 contact3433 logTwoBall

theorem center_sq3433 : (center3433.re : ℝ)^2 +
    (center3433.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3433]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3433 : work3433.theta.ok = true ∧
    work3433.jac.invOK = true ∧ acceptsUnitSq work3433.out = true := by decide +kernel

def cell3433 : CellCertificate where
  tauBall := tau3433
  contactCenter := center3433
  contactBall := contact3433
  work := work3433
  center_sq := center_sq3433
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3433.1
  jac_ok := checks3433.2.1
  accepted := checks3433.2.2

def tau3434 : RatBall :=
  ⟨⟨-43/640, 253/640⟩, 3/1280⟩
def center3434 : GaussianRat :=
  ⟨-55396349/1000000000, 28864989/100000000⟩
def contact3434 : RatBall := localContactBall tau3434 center3434
def work3434 : RoundedTauEval :=
  evalTau precision tau3434 contact3434 logTwoBall

theorem center_sq3434 : (center3434.re : ℝ)^2 +
    (center3434.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3434]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3434 : work3434.theta.ok = true ∧
    work3434.jac.invOK = true ∧ acceptsUnitSq work3434.out = true := by decide +kernel

def cell3434 : CellCertificate where
  tauBall := tau3434
  contactCenter := center3434
  contactBall := contact3434
  work := work3434
  center_sq := center_sq3434
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3434.1
  jac_ok := checks3434.2.1
  accepted := checks3434.2.2

def tau3435 : RatBall :=
  ⟨⟨-41/640, 253/640⟩, 3/1280⟩
def center3435 : GaussianRat :=
  ⟨-52835321/1000000000, 11552523/40000000⟩
def contact3435 : RatBall := localContactBall tau3435 center3435
def work3435 : RoundedTauEval :=
  evalTau precision tau3435 contact3435 logTwoBall

theorem center_sq3435 : (center3435.re : ℝ)^2 +
    (center3435.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3435]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3435 : work3435.theta.ok = true ∧
    work3435.jac.invOK = true ∧ acceptsUnitSq work3435.out = true := by decide +kernel

def cell3435 : CellCertificate where
  tauBall := tau3435
  contactCenter := center3435
  contactBall := contact3435
  work := work3435
  center_sq := center_sq3435
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3435.1
  jac_ok := checks3435.2.1
  accepted := checks3435.2.2

def tau3436 : RatBall :=
  ⟨⟨-39/640, 249/640⟩, 3/1280⟩
def center3436 : GaussianRat :=
  ⟨-4997259/100000000, 17740947/62500000⟩
def contact3436 : RatBall := localContactBall tau3436 center3436
def work3436 : RoundedTauEval :=
  evalTau precision tau3436 contact3436 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429


