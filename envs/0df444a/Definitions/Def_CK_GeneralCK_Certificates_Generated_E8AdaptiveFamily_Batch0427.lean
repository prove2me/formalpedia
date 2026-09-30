-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0427
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0427
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:08:08.221443+00:00
-- url     : https://prove2.me/theorems/d6ae0117-0f04-4225-bf07-9b9cb7f4c1cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0427.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0427_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3420 : (center3420.re : ℝ)^2 +
    (center3420.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3420]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3420 : work3420.theta.ok = true ∧
    work3420.jac.invOK = true ∧ acceptsUnitSq work3420.out = true := by decide +kernel

def cell3420 : CellCertificate where
  tauBall := tau3420
  contactCenter := center3420
  contactBall := contact3420
  work := work3420
  center_sq := center_sq3420
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3420.1
  jac_ok := checks3420.2.1
  accepted := checks3420.2.2

def tau3421 : RatBall :=
  ⟨⟨-7/128, 49/128⟩, 3/1280⟩
def center3421 : GaussianRat :=
  ⟨-44607937/1000000000, 279044067/1000000000⟩
def contact3421 : RatBall := localContactBall tau3421 center3421
def work3421 : RoundedTauEval :=
  evalTau precision tau3421 contact3421 logTwoBall

theorem center_sq3421 : (center3421.re : ℝ)^2 +
    (center3421.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3421]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3421 : work3421.theta.ok = true ∧
    work3421.jac.invOK = true ∧ acceptsUnitSq work3421.out = true := by decide +kernel

def cell3421 : CellCertificate where
  tauBall := tau3421
  contactCenter := center3421
  contactBall := contact3421
  work := work3421
  center_sq := center_sq3421
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3421.1
  jac_ok := checks3421.2.1
  accepted := checks3421.2.2

def tau3422 : RatBall :=
  ⟨⟨-33/640, 49/128⟩, 3/1280⟩
def center3422 : GaussianRat :=
  ⟨-42068541/1000000000, 27916967/100000000⟩
def contact3422 : RatBall := localContactBall tau3422 center3422
def work3422 : RoundedTauEval :=
  evalTau precision tau3422 contact3422 logTwoBall

theorem center_sq3422 : (center3422.re : ℝ)^2 +
    (center3422.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3422]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3422 : work3422.theta.ok = true ∧
    work3422.jac.invOK = true ∧ acceptsUnitSq work3422.out = true := by decide +kernel

def cell3422 : CellCertificate where
  tauBall := tau3422
  contactCenter := center3422
  contactBall := contact3422
  work := work3422
  center_sq := center_sq3422
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3422.1
  jac_ok := checks3422.2.1
  accepted := checks3422.2.2

def tau3423 : RatBall :=
  ⟨⟨-7/128, 247/640⟩, 3/1280⟩
def center3423 : GaussianRat :=
  ⟨-2796129/62500000, 281586221/1000000000⟩
def contact3423 : RatBall := localContactBall tau3423 center3423
def work3423 : RoundedTauEval :=
  evalTau precision tau3423 contact3423 logTwoBall

theorem center_sq3423 : (center3423.re : ℝ)^2 +
    (center3423.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3423]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3423 : work3423.theta.ok = true ∧
    work3423.jac.invOK = true ∧ acceptsUnitSq work3423.out = true := by decide +kernel

def cell3423 : CellCertificate where
  tauBall := tau3423
  contactCenter := center3423
  contactBall := contact3423
  work := work3423
  center_sq := center_sq3423
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3423.1
  jac_ok := checks3423.2.1
  accepted := checks3423.2.2

def cells : List CellCertificate := [cell3416, cell3417, cell3418, cell3419, cell3420, cell3421, cell3422, cell3423]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427


