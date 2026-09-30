-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0417
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0417
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:10:46.335638+00:00
-- url     : https://prove2.me/theorems/5569a7c6-d80e-45b0-b9df-f25d2626d97a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0417.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0417_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3340 : RoundedTauEval :=
  evalTau precision tau3340 contact3340 logTwoBall

theorem center_sq3340 : (center3340.re : ℝ)^2 +
    (center3340.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3340]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3340 : work3340.theta.ok = true ∧
    work3340.jac.invOK = true ∧ acceptsUnitSq work3340.out = true := by decide +kernel

def cell3340 : CellCertificate where
  tauBall := tau3340
  contactCenter := center3340
  contactBall := contact3340
  work := work3340
  center_sq := center_sq3340
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3340.1
  jac_ok := checks3340.2.1
  accepted := checks3340.2.2

def tau3341 : RatBall :=
  ⟨⟨-73/640, 243/640⟩, 3/1280⟩
def center3341 : GaussianRat :=
  ⟨-46073697/500000000, 54566443/200000000⟩
def contact3341 : RatBall := localContactBall tau3341 center3341
def work3341 : RoundedTauEval :=
  evalTau precision tau3341 contact3341 logTwoBall

theorem center_sq3341 : (center3341.re : ℝ)^2 +
    (center3341.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3341]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3341 : work3341.theta.ok = true ∧
    work3341.jac.invOK = true ∧ acceptsUnitSq work3341.out = true := by decide +kernel

def cell3341 : CellCertificate where
  tauBall := tau3341
  contactCenter := center3341
  contactBall := contact3341
  work := work3341
  center_sq := center_sq3341
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3341.1
  jac_ok := checks3341.2.1
  accepted := checks3341.2.2

def tau3342 : RatBall :=
  ⟨⟨-77/640, 49/128⟩, 3/1280⟩
def center3342 : GaussianRat :=
  ⟨-24343527/250000000, 34347651/125000000⟩
def contact3342 : RatBall := localContactBall tau3342 center3342
def work3342 : RoundedTauEval :=
  evalTau precision tau3342 contact3342 logTwoBall

theorem center_sq3342 : (center3342.re : ℝ)^2 +
    (center3342.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3342]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3342 : work3342.theta.ok = true ∧
    work3342.jac.invOK = true ∧ acceptsUnitSq work3342.out = true := by decide +kernel

def cell3342 : CellCertificate where
  tauBall := tau3342
  contactCenter := center3342
  contactBall := contact3342
  work := work3342
  center_sq := center_sq3342
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3342.1
  jac_ok := checks3342.2.1
  accepted := checks3342.2.2

def tau3343 : RatBall :=
  ⟨⟨-15/128, 49/128⟩, 3/1280⟩
def center3343 : GaussianRat :=
  ⟨-9489219/100000000, 275052007/1000000000⟩
def contact3343 : RatBall := localContactBall tau3343 center3343
def work3343 : RoundedTauEval :=
  evalTau precision tau3343 contact3343 logTwoBall

theorem center_sq3343 : (center3343.re : ℝ)^2 +
    (center3343.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3343]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3343 : work3343.theta.ok = true ∧
    work3343.jac.invOK = true ∧ acceptsUnitSq work3343.out = true := by decide +kernel

def cell3343 : CellCertificate where
  tauBall := tau3343
  contactCenter := center3343
  contactBall := contact3343
  work := work3343
  center_sq := center_sq3343
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3343.1
  jac_ok := checks3343.2.1
  accepted := checks3343.2.2

def cells : List CellCertificate := [cell3336, cell3337, cell3338, cell3339, cell3340, cell3341, cell3342, cell3343]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417


