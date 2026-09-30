-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0439_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0439_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:24:47.76669+00:00
-- url     : https://prove2.me/theorems/c8f156c1-1b24-4ff8-a2b9-0b47ebbeae02
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0439 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0439 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0439 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0439 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0439 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0439

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3512 : RatBall :=
  ⟨⟨-3/640, 249/640⟩, 3/1280⟩
def center3512 : GaussianRat :=
  ⟨-3854079/1000000000, 142647681/500000000⟩
def contact3512 : RatBall := localContactBall tau3512 center3512
def work3512 : RoundedTauEval :=
  evalTau precision tau3512 contact3512 logTwoBall

theorem center_sq3512 : (center3512.re : ℝ)^2 +
    (center3512.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3512]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3512 : work3512.theta.ok = true ∧
    work3512.jac.invOK = true ∧ acceptsUnitSq work3512.out = true := by decide +kernel

def cell3512 : CellCertificate where
  tauBall := tau3512
  contactCenter := center3512
  contactBall := contact3512
  work := work3512
  center_sq := center_sq3512
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3512.1
  jac_ok := checks3512.2.1
  accepted := checks3512.2.2

def tau3513 : RatBall :=
  ⟨⟨-1/640, 249/640⟩, 3/1280⟩
def center3513 : GaussianRat :=
  ⟨-1284711/1000000000, 285303029/1000000000⟩
def contact3513 : RatBall := localContactBall tau3513 center3513
def work3513 : RoundedTauEval :=
  evalTau precision tau3513 contact3513 logTwoBall

theorem center_sq3513 : (center3513.re : ℝ)^2 +
    (center3513.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3513]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3513 : work3513.theta.ok = true ∧
    work3513.jac.invOK = true ∧ acceptsUnitSq work3513.out = true := by decide +kernel

def cell3513 : CellCertificate where
  tauBall := tau3513
  contactCenter := center3513
  contactBall := contact3513
  work := work3513
  center_sq := center_sq3513
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3513.1
  jac_ok := checks3513.2.1
  accepted := checks3513.2.2

def tau3514 : RatBall :=
  ⟨⟨-3/640, 251/640⟩, 3/1280⟩
def center3514 : GaussianRat :=
  ⟨-193283/50000000, 143934259/500000000⟩
def contact3514 : RatBall := localContactBall tau3514 center3514
def work3514 : RoundedTauEval :=
  evalTau precision tau3514 contact3514 logTwoBall

theorem center_sq3514 : (center3514.re : ℝ)^2 +
    (center3514.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3514]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3514 : work3514.theta.ok = true ∧
    work3514.jac.invOK = true ∧ acceptsUnitSq work3514.out = true := by decide +kernel

def cell3514 : CellCertificate where
  tauBall := tau3514
  contactCenter := center3514
  contactBall := contact3514
  work := work3514
  center_sq := center_sq3514
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3514.1
  jac_ok := checks3514.2.1
  accepted := checks3514.2.2

def tau3515 : RatBall :=
  ⟨⟨-1/640, 251/640⟩, 3/1280⟩
def center3515 : GaussianRat :=
  ⟨-1288571/1000000000, 287876293/1000000000⟩
def contact3515 : RatBall := localContactBall tau3515 center3515
def work3515 : RoundedTauEval :=
  evalTau precision tau3515 contact3515 logTwoBall

theorem center_sq3515 : (center3515.re : ℝ)^2 +
    (center3515.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3515]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3515 : work3515.theta.ok = true ∧
    work3515.jac.invOK = true ∧ acceptsUnitSq work3515.out = true := by decide +kernel

def cell3515 : CellCertificate where
  tauBall := tau3515
  contactCenter := center3515
  contactBall := contact3515
  work := work3515
  center_sq := center_sq3515
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3515.1
  jac_ok := checks3515.2.1
  accepted := checks3515.2.2

def tau3516 : RatBall :=
  ⟨⟨-7/640, 253/640⟩, 3/1280⟩
def center3516 : GaussianRat :=
  ⟨-9046633/1000000000, 145205019/500000000⟩
def contact3516 : RatBall := localContactBall tau3516 center3516
def work3516 : RoundedTauEval :=
  evalTau precision tau3516 contact3516 logTwoBall

theorem center_sq3516 : (center3516.re : ℝ)^2 +
    (center3516.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3516]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3516 : work3516.theta.ok = true ∧
    work3516.jac.invOK = true ∧ acceptsUnitSq work3516.out = true := by decide +kernel

def cell3516 : CellCertificate where
  tauBall := tau3516
  contactCenter := center3516
  contactBall := contact3516
  work := work3516
  center_sq := center_sq3516
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3516.1
  jac_ok := checks3516.2.1
  accepted := checks3516.2.2

def tau3517 : RatBall :=
  ⟨⟨-1/128, 253/640⟩, 3/1280⟩
def center3517 : GaussianRat :=
  ⟨-1292431/200000000, 290433683/1000000000⟩
def contact3517 : RatBall := localContactBall tau3517 center3517
def work3517 : RoundedTauEval :=
  evalTau precision tau3517 contact3517 logTwoBall

theorem center_sq3517 : (center3517.re : ℝ)^2 +
    (center3517.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3517]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3517 : work3517.theta.ok = true ∧
    work3517.jac.invOK = true ∧ acceptsUnitSq work3517.out = true := by decide +kernel

def cell3517 : CellCertificate where
  tauBall := tau3517
  contactCenter := center3517
  contactBall := contact3517
  work := work3517
  center_sq := center_sq3517
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3517.1
  jac_ok := checks3517.2.1
  accepted := checks3517.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0439


