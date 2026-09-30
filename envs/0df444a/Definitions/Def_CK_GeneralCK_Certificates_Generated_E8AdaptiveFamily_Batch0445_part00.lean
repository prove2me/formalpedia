-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0445_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0445_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:07:43.209662+00:00
-- url     : https://prove2.me/theorems/ac247940-935b-4924-9930-a9eb20c5ea48
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445 (part 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445 (part 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445 (part 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445 (part 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0445 (part 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3560 : RatBall :=
  ⟨⟨5/128, 49/128⟩, 3/1280⟩
def center3560 : GaussianRat :=
  ⟨31895051/1000000000, 13979961/50000000⟩
def contact3560 : RatBall := localContactBall tau3560 center3560
def work3560 : RoundedTauEval :=
  evalTau precision tau3560 contact3560 logTwoBall

theorem center_sq3560 : (center3560.re : ℝ)^2 +
    (center3560.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3560]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3560 : work3560.theta.ok = true ∧
    work3560.jac.invOK = true ∧ acceptsUnitSq work3560.out = true := by decide +kernel

def cell3560 : CellCertificate where
  tauBall := tau3560
  contactCenter := center3560
  contactBall := contact3560
  work := work3560
  center_sq := center_sq3560
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3560.1
  jac_ok := checks3560.2.1
  accepted := checks3560.2.2

def tau3561 : RatBall :=
  ⟨⟨27/640, 49/128⟩, 3/1280⟩
def center3561 : GaussianRat :=
  ⟨1076269/31250000, 69875701/250000000⟩
def contact3561 : RatBall := localContactBall tau3561 center3561
def work3561 : RoundedTauEval :=
  evalTau precision tau3561 contact3561 logTwoBall

theorem center_sq3561 : (center3561.re : ℝ)^2 +
    (center3561.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3561]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3561 : work3561.theta.ok = true ∧
    work3561.jac.invOK = true ∧ acceptsUnitSq work3561.out = true := by decide +kernel

def cell3561 : CellCertificate where
  tauBall := tau3561
  contactCenter := center3561
  contactBall := contact3561
  work := work3561
  center_sq := center_sq3561
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3561.1
  jac_ok := checks3561.2.1
  accepted := checks3561.2.2

def tau3562 : RatBall :=
  ⟨⟨5/128, 247/640⟩, 3/1280⟩
def center3562 : GaussianRat :=
  ⟨7997111/250000000, 282149129/1000000000⟩
def contact3562 : RatBall := localContactBall tau3562 center3562
def work3562 : RoundedTauEval :=
  evalTau precision tau3562 contact3562 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445


