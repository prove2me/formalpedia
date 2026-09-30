-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0398_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0398_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:50:37.929452+00:00
-- url     : https://prove2.me/theorems/36ac047b-c211-4ec2-b9bd-c429d14b6912
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0398 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0398_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3188 : RatBall :=
  ⟨⟨127/640, -221/640⟩, 3/1280⟩
def center3188 : GaussianRat :=
  ⟨38341447/250000000, -29753309/125000000⟩
def contact3188 : RatBall := localContactBall tau3188 center3188
def work3188 : RoundedTauEval :=
  evalTau precision tau3188 contact3188 logTwoBall

theorem center_sq3188 : (center3188.re : ℝ)^2 +
    (center3188.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3188]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3188 : work3188.theta.ok = true ∧
    work3188.jac.invOK = true ∧ acceptsUnitSq work3188.out = true := by decide +kernel

def cell3188 : CellCertificate where
  tauBall := tau3188
  contactCenter := center3188
  contactBall := contact3188
  work := work3188
  center_sq := center_sq3188
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3188.1
  jac_ok := checks3188.2.1
  accepted := checks3188.2.2

def tau3189 : RatBall :=
  ⟨⟨129/640, -221/640⟩, 3/1280⟩
def center3189 : GaussianRat :=
  ⟨155670749/1000000000, -118833343/500000000⟩
def contact3189 : RatBall := localContactBall tau3189 center3189
def work3189 : RoundedTauEval :=
  evalTau precision tau3189 contact3189 logTwoBall

theorem center_sq3189 : (center3189.re : ℝ)^2 +
    (center3189.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3189]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3189 : work3189.theta.ok = true ∧
    work3189.jac.invOK = true ∧ acceptsUnitSq work3189.out = true := by decide +kernel

def cell3189 : CellCertificate where
  tauBall := tau3189
  contactCenter := center3189
  contactBall := contact3189
  work := work3189
  center_sq := center_sq3189
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3189.1
  jac_ok := checks3189.2.1
  accepted := checks3189.2.2

def tau3190 : RatBall :=
  ⟨⟨131/640, -221/640⟩, 3/1280⟩
def center3190 : GaussianRat :=
  ⟨157970893/1000000000, -237302543/1000000000⟩
def contact3190 : RatBall := localContactBall tau3190 center3190
def work3190 : RoundedTauEval :=
  evalTau precision tau3190 contact3190 logTwoBall

theorem center_sq3190 : (center3190.re : ℝ)^2 +
    (center3190.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3190]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3190 : work3190.theta.ok = true ∧
    work3190.jac.invOK = true ∧ acceptsUnitSq work3190.out = true := by decide +kernel

def cell3190 : CellCertificate where
  tauBall := tau3190
  contactCenter := center3190
  contactBall := contact3190
  work := work3190
  center_sq := center_sq3190
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3190.1
  jac_ok := checks3190.2.1
  accepted := checks3190.2.2

def tau3191 : RatBall :=
  ⟨⟨129/640, -219/640⟩, 3/1280⟩
def center3191 : GaussianRat :=
  ⟨155311177/1000000000, -29420787/125000000⟩
def contact3191 : RatBall := localContactBall tau3191 center3191
def work3191 : RoundedTauEval :=
  evalTau precision tau3191 contact3191 logTwoBall

theorem center_sq3191 : (center3191.re : ℝ)^2 +
    (center3191.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3191]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3191 : work3191.theta.ok = true ∧
    work3191.jac.invOK = true ∧ acceptsUnitSq work3191.out = true := by decide +kernel

def cell3191 : CellCertificate where
  tauBall := tau3191
  contactCenter := center3191
  contactBall := contact3191
  work := work3191
  center_sq := center_sq3191
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3191.1
  jac_ok := checks3191.2.1
  accepted := checks3191.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398


