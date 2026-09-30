-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0445_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0445_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:39:10.365977+00:00
-- url     : https://prove2.me/theorems/07bdbb00-72b8-4891-b673-337fd96f2508
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0445 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0445_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center3565 : GaussianRat :=
  ⟨19763727/500000000, 279288009/1000000000⟩
def contact3565 : RatBall := localContactBall tau3565 center3565
def work3565 : RoundedTauEval :=
  evalTau precision tau3565 contact3565 logTwoBall

theorem center_sq3565 : (center3565.re : ℝ)^2 +
    (center3565.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3565]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3565 : work3565.theta.ok = true ∧
    work3565.jac.invOK = true ∧ acceptsUnitSq work3565.out = true := by decide +kernel

def cell3565 : CellCertificate where
  tauBall := tau3565
  contactCenter := center3565
  contactBall := contact3565
  work := work3565
  center_sq := center_sq3565
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3565.1
  jac_ok := checks3565.2.1
  accepted := checks3565.2.2

def tau3566 : RatBall :=
  ⟨⟨29/640, 247/640⟩, 3/1280⟩
def center3566 : GaussianRat :=
  ⟨18546463/500000000, 281946171/1000000000⟩
def contact3566 : RatBall := localContactBall tau3566 center3566
def work3566 : RoundedTauEval :=
  evalTau precision tau3566 contact3566 logTwoBall

theorem center_sq3566 : (center3566.re : ℝ)^2 +
    (center3566.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3566]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3566 : work3566.theta.ok = true ∧
    work3566.jac.invOK = true ∧ acceptsUnitSq work3566.out = true := by decide +kernel

def cell3566 : CellCertificate where
  tauBall := tau3566
  contactCenter := center3566
  contactBall := contact3566
  work := work3566
  center_sq := center_sq3566
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3566.1
  jac_ok := checks3566.2.1
  accepted := checks3566.2.2

def tau3567 : RatBall :=
  ⟨⟨31/640, 247/640⟩, 3/1280⟩
def center3567 : GaussianRat :=
  ⟨4955369/125000000, 8807299/31250000⟩
def contact3567 : RatBall := localContactBall tau3567 center3567
def work3567 : RoundedTauEval :=
  evalTau precision tau3567 contact3567 logTwoBall

theorem center_sq3567 : (center3567.re : ℝ)^2 +
    (center3567.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3567]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445


