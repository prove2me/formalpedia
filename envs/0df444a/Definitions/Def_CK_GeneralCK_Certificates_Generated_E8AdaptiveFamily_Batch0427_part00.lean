-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0427_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0427_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:14:02.662798+00:00
-- url     : https://prove2.me/theorems/addad0d9-4290-49d7-80d4-80f90f3b526e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0427 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3416 : RatBall :=
  ⟨⟨-41/640, 247/640⟩, 3/1280⟩
def center3416 : GaussianRat :=
  ⟨-52366871/1000000000, 70290053/250000000⟩
def contact3416 : RatBall := localContactBall tau3416 center3416
def work3416 : RoundedTauEval :=
  evalTau precision tau3416 contact3416 logTwoBall

theorem center_sq3416 : (center3416.re : ℝ)^2 +
    (center3416.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3416]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3416 : work3416.theta.ok = true ∧
    work3416.jac.invOK = true ∧ acceptsUnitSq work3416.out = true := by decide +kernel

def cell3416 : CellCertificate where
  tauBall := tau3416
  contactCenter := center3416
  contactBall := contact3416
  work := work3416
  center_sq := center_sq3416
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3416.1
  jac_ok := checks3416.2.1
  accepted := checks3416.2.2

def tau3417 : RatBall :=
  ⟨⟨-39/640, 49/128⟩, 3/1280⟩
def center3417 : GaussianRat :=
  ⟨-49681259/1000000000, 139385581/500000000⟩
def contact3417 : RatBall := localContactBall tau3417 center3417
def work3417 : RoundedTauEval :=
  evalTau precision tau3417 contact3417 logTwoBall

theorem center_sq3417 : (center3417.re : ℝ)^2 +
    (center3417.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3417]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3417 : work3417.theta.ok = true ∧
    work3417.jac.invOK = true ∧ acceptsUnitSq work3417.out = true := by decide +kernel

def cell3417 : CellCertificate where
  tauBall := tau3417
  contactCenter := center3417
  contactBall := contact3417
  work := work3417
  center_sq := center_sq3417
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3417.1
  jac_ok := checks3417.2.1
  accepted := checks3417.2.2

def tau3418 : RatBall :=
  ⟨⟨-37/640, 49/128⟩, 3/1280⟩
def center3418 : GaussianRat :=
  ⟨-23572771/500000000, 278911223/1000000000⟩
def contact3418 : RatBall := localContactBall tau3418 center3418
def work3418 : RoundedTauEval :=
  evalTau precision tau3418 contact3418 logTwoBall

theorem center_sq3418 : (center3418.re : ℝ)^2 +
    (center3418.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3418]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3418 : work3418.theta.ok = true ∧
    work3418.jac.invOK = true ∧ acceptsUnitSq work3418.out = true := by decide +kernel

def cell3418 : CellCertificate where
  tauBall := tau3418
  contactCenter := center3418
  contactBall := contact3418
  work := work3418
  center_sq := center_sq3418
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3418.1
  jac_ok := checks3418.2.1
  accepted := checks3418.2.2

def tau3419 : RatBall :=
  ⟨⟨-39/640, 247/640⟩, 3/1280⟩
def center3419 : GaussianRat :=
  ⟨-49825917/1000000000, 281309513/1000000000⟩
def contact3419 : RatBall := localContactBall tau3419 center3419
def work3419 : RoundedTauEval :=
  evalTau precision tau3419 contact3419 logTwoBall

theorem center_sq3419 : (center3419.re : ℝ)^2 +
    (center3419.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3419]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3419 : work3419.theta.ok = true ∧
    work3419.jac.invOK = true ∧ acceptsUnitSq work3419.out = true := by decide +kernel

def cell3419 : CellCertificate where
  tauBall := tau3419
  contactCenter := center3419
  contactBall := contact3419
  work := work3419
  center_sq := center_sq3419
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3419.1
  jac_ok := checks3419.2.1
  accepted := checks3419.2.2

def tau3420 : RatBall :=
  ⟨⟨-37/640, 247/640⟩, 3/1280⟩
def center3420 : GaussianRat :=
  ⟨-11820737/250000000, 11258061/40000000⟩
def contact3420 : RatBall := localContactBall tau3420 center3420
def work3420 : RoundedTauEval :=
  evalTau precision tau3420 contact3420 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427


