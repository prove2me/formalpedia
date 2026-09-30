-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0419
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0419
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:38:24.558765+00:00
-- url     : https://prove2.me/theorems/6c558cae-bdb8-4606-a493-b166d4885084
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0419.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0419_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3356 : RoundedTauEval :=
  evalTau precision tau3356 contact3356 logTwoBall

theorem center_sq3356 : (center3356.re : ℝ)^2 +
    (center3356.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3356]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3356 : work3356.theta.ok = true ∧
    work3356.jac.invOK = true ∧ acceptsUnitSq work3356.out = true := by decide +kernel

def cell3356 : CellCertificate where
  tauBall := tau3356
  contactCenter := center3356
  contactBall := contact3356
  work := work3356
  center_sq := center_sq3356
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3356.1
  jac_ok := checks3356.2.1
  accepted := checks3356.2.2

def tau3357 : RatBall :=
  ⟨⟨-67/640, 49/128⟩, 3/1280⟩
def center3357 : GaussianRat :=
  ⟨-42464509/500000000, 34508699/125000000⟩
def contact3357 : RatBall := localContactBall tau3357 center3357
def work3357 : RoundedTauEval :=
  evalTau precision tau3357 contact3357 logTwoBall

theorem center_sq3357 : (center3357.re : ℝ)^2 +
    (center3357.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3357]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3357 : work3357.theta.ok = true ∧
    work3357.jac.invOK = true ∧ acceptsUnitSq work3357.out = true := by decide +kernel

def cell3357 : CellCertificate where
  tauBall := tau3357
  contactCenter := center3357
  contactBall := contact3357
  work := work3357
  center_sq := center_sq3357
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3357.1
  jac_ok := checks3357.2.1
  accepted := checks3357.2.2

def tau3358 : RatBall :=
  ⟨⟨-13/128, 49/128⟩, 3/1280⟩
def center3358 : GaussianRat :=
  ⟨-41214889/500000000, 1726921/6250000⟩
def contact3358 : RatBall := localContactBall tau3358 center3358
def work3358 : RoundedTauEval :=
  evalTau precision tau3358 contact3358 logTwoBall

theorem center_sq3358 : (center3358.re : ℝ)^2 +
    (center3358.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3358]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3358 : work3358.theta.ok = true ∧
    work3358.jac.invOK = true ∧ acceptsUnitSq work3358.out = true := by decide +kernel

def cell3358 : CellCertificate where
  tauBall := tau3358
  contactCenter := center3358
  contactBall := contact3358
  work := work3358
  center_sq := center_sq3358
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3358.1
  jac_ok := checks3358.2.1
  accepted := checks3358.2.2

def tau3359 : RatBall :=
  ⟨⟨-67/640, 247/640⟩, 3/1280⟩
def center3359 : GaussianRat :=
  ⟨-42585897/500000000, 278570563/1000000000⟩
def contact3359 : RatBall := localContactBall tau3359 center3359
def work3359 : RoundedTauEval :=
  evalTau precision tau3359 contact3359 logTwoBall

theorem center_sq3359 : (center3359.re : ℝ)^2 +
    (center3359.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3359]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3359 : work3359.theta.ok = true ∧
    work3359.jac.invOK = true ∧ acceptsUnitSq work3359.out = true := by decide +kernel

def cell3359 : CellCertificate where
  tauBall := tau3359
  contactCenter := center3359
  contactBall := contact3359
  work := work3359
  center_sq := center_sq3359
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3359.1
  jac_ok := checks3359.2.1
  accepted := checks3359.2.2

def cells : List CellCertificate := [cell3352, cell3353, cell3354, cell3355, cell3356, cell3357, cell3358, cell3359]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419


