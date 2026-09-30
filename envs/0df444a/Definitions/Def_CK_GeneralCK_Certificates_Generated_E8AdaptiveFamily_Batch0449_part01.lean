-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0449_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0449_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:03:30.863724+00:00
-- url     : https://prove2.me/theorems/1e707e65-1034-49ee-a13f-909aa0b13954
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0449 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0449_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3594 : work3594.theta.ok = true ∧
    work3594.jac.invOK = true ∧ acceptsUnitSq work3594.out = true := by decide +kernel

def cell3594 : CellCertificate where
  tauBall := tau3594
  contactCenter := center3594
  contactBall := contact3594
  work := work3594
  center_sq := center_sq3594
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3594.1
  jac_ok := checks3594.2.1
  accepted := checks3594.2.2

def tau3595 : RatBall :=
  ⟨⟨27/640, 51/128⟩, 3/1280⟩
def center3595 : GaussianRat :=
  ⟨34958801/1000000000, 14616047/50000000⟩
def contact3595 : RatBall := localContactBall tau3595 center3595
def work3595 : RoundedTauEval :=
  evalTau precision tau3595 contact3595 logTwoBall

theorem center_sq3595 : (center3595.re : ℝ)^2 +
    (center3595.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3595]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3595 : work3595.theta.ok = true ∧
    work3595.jac.invOK = true ∧ acceptsUnitSq work3595.out = true := by decide +kernel

def cell3595 : CellCertificate where
  tauBall := tau3595
  contactCenter := center3595
  contactBall := contact3595
  work := work3595
  center_sq := center_sq3595
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3595.1
  jac_ok := checks3595.2.1
  accepted := checks3595.2.2

def tau3596 : RatBall :=
  ⟨⟨29/640, 253/640⟩, 3/1280⟩
def center3596 : GaussianRat :=
  ⟨18713263/500000000, 289632371/1000000000⟩
def contact3596 : RatBall := localContactBall tau3596 center3596
def work3596 : RoundedTauEval :=
  evalTau precision tau3596 contact3596 logTwoBall

theorem center_sq3596 : (center3596.re : ℝ)^2 +
    (center3596.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3596]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3596 : work3596.theta.ok = true ∧
    work3596.jac.invOK = true ∧ acceptsUnitSq work3596.out = true := by decide +kernel

def cell3596 : CellCertificate where
  tauBall := tau3596
  contactCenter := center3596
  contactBall := contact3596
  work := work3596
  center_sq := center_sq3596
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3596.1
  jac_ok := checks3596.2.1
  accepted := checks3596.2.2

def tau3597 : RatBall :=
  ⟨⟨31/640, 253/640⟩, 3/1280⟩
def center3597 : GaussianRat :=
  ⟨9999803/250000000, 36189373/125000000⟩
def contact3597 : RatBall := localContactBall tau3597 center3597

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449


