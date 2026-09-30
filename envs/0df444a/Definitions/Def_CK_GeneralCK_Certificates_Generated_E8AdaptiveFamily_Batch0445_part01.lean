-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0445_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0445_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:20:08.851264+00:00
-- url     : https://prove2.me/theorems/c98f04ad-72fd-45fc-9a09-bea173efe6e3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0445 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0445_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3562 : (center3562.re : ℝ)^2 +
    (center3562.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3562]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3562 : work3562.theta.ok = true ∧
    work3562.jac.invOK = true ∧ acceptsUnitSq work3562.out = true := by decide +kernel

def cell3562 : CellCertificate where
  tauBall := tau3562
  contactCenter := center3562
  contactBall := contact3562
  work := work3562
  center_sq := center_sq3562
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3562.1
  jac_ok := checks3562.2.1
  accepted := checks3562.2.2

def tau3563 : RatBall :=
  ⟨⟨27/640, 247/640⟩, 3/1280⟩
def center3563 : GaussianRat :=
  ⟨34541389/1000000000, 56410273/200000000⟩
def contact3563 : RatBall := localContactBall tau3563 center3563
def work3563 : RoundedTauEval :=
  evalTau precision tau3563 contact3563 logTwoBall

theorem center_sq3563 : (center3563.re : ℝ)^2 +
    (center3563.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3563]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3563 : work3563.theta.ok = true ∧
    work3563.jac.invOK = true ∧ acceptsUnitSq work3563.out = true := by decide +kernel

def cell3563 : CellCertificate where
  tauBall := tau3563
  contactCenter := center3563
  contactBall := contact3563
  work := work3563
  center_sq := center_sq3563
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3563.1
  jac_ok := checks3563.2.1
  accepted := checks3563.2.2

def tau3564 : RatBall :=
  ⟨⟨29/640, 49/128⟩, 3/1280⟩
def center3564 : GaussianRat :=
  ⟨4623097/125000000, 13969953/50000000⟩
def contact3564 : RatBall := localContactBall tau3564 center3564
def work3564 : RoundedTauEval :=
  evalTau precision tau3564 contact3564 logTwoBall

theorem center_sq3564 : (center3564.re : ℝ)^2 +
    (center3564.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3564]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3564 : work3564.theta.ok = true ∧
    work3564.jac.invOK = true ∧ acceptsUnitSq work3564.out = true := by decide +kernel

def cell3564 : CellCertificate where
  tauBall := tau3564
  contactCenter := center3564
  contactBall := contact3564
  work := work3564
  center_sq := center_sq3564
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3564.1
  jac_ok := checks3564.2.1
  accepted := checks3564.2.2

def tau3565 : RatBall :=
  ⟨⟨31/640, 49/128⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445


