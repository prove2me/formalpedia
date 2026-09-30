-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0448_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0448_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:11:13.695735+00:00
-- url     : https://prove2.me/theorems/33ded3e9-a4f3-47d7-bd7e-f1550e5b6bbe
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0448 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3584 : RatBall :=
  ⟨⟨5/128, 249/640⟩, 3/1280⟩
def center3584 : GaussianRat :=
  ⟨32083143/1000000000, 142353243/500000000⟩
def contact3584 : RatBall := localContactBall tau3584 center3584
def work3584 : RoundedTauEval :=
  evalTau precision tau3584 contact3584 logTwoBall

theorem center_sq3584 : (center3584.re : ℝ)^2 +
    (center3584.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3584]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3584 : work3584.theta.ok = true ∧
    work3584.jac.invOK = true ∧ acceptsUnitSq work3584.out = true := by decide +kernel

def cell3584 : CellCertificate where
  tauBall := tau3584
  contactCenter := center3584
  contactBall := contact3584
  work := work3584
  center_sq := center_sq3584
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3584.1
  jac_ok := checks3584.2.1
  accepted := checks3584.2.2

def tau3585 : RatBall :=
  ⟨⟨27/640, 249/640⟩, 3/1280⟩
def center3585 : GaussianRat :=
  ⟨34643579/1000000000, 56921471/200000000⟩
def contact3585 : RatBall := localContactBall tau3585 center3585
def work3585 : RoundedTauEval :=
  evalTau precision tau3585 contact3585 logTwoBall

theorem center_sq3585 : (center3585.re : ℝ)^2 +
    (center3585.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3585]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3585 : work3585.theta.ok = true ∧
    work3585.jac.invOK = true ∧ acceptsUnitSq work3585.out = true := by decide +kernel

def cell3585 : CellCertificate where
  tauBall := tau3585
  contactCenter := center3585
  contactBall := contact3585
  work := work3585
  center_sq := center_sq3585
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3585.1
  jac_ok := checks3585.2.1
  accepted := checks3585.2.2

def tau3586 : RatBall :=
  ⟨⟨5/128, 251/640⟩, 3/1280⟩
def center3586 : GaussianRat :=
  ⟨32179167/1000000000, 57454279/200000000⟩
def contact3586 : RatBall := localContactBall tau3586 center3586
def work3586 : RoundedTauEval :=
  evalTau precision tau3586 contact3586 logTwoBall

theorem center_sq3586 : (center3586.re : ℝ)^2 +
    (center3586.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3586]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3586 : work3586.theta.ok = true ∧
    work3586.jac.invOK = true ∧ acceptsUnitSq work3586.out = true := by decide +kernel

def cell3586 : CellCertificate where
  tauBall := tau3586
  contactCenter := center3586
  contactBall := contact3586
  work := work3586
  center_sq := center_sq3586
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3586.1
  jac_ok := checks3586.2.1
  accepted := checks3586.2.2

def tau3587 : RatBall :=
  ⟨⟨27/640, 251/640⟩, 3/1280⟩
def center3587 : GaussianRat :=
  ⟨17373599/500000000, 287170877/1000000000⟩
def contact3587 : RatBall := localContactBall tau3587 center3587
def work3587 : RoundedTauEval :=
  evalTau precision tau3587 contact3587 logTwoBall

theorem center_sq3587 : (center3587.re : ℝ)^2 +
    (center3587.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3587]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448


