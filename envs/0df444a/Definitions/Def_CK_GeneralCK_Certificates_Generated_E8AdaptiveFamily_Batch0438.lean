-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0438
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0438
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:49:17.348603+00:00
-- url     : https://prove2.me/theorems/73877a70-b3a0-40b3-a3c0-f6954e44e047
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0438.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0438_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3510 : RatBall :=
  ⟨⟨-7/640, 251/640⟩, 3/1280⟩
def center3510 : GaussianRat :=
  ⟨-9019241/1000000000, 287829653/1000000000⟩
def contact3510 : RatBall := localContactBall tau3510 center3510
def work3510 : RoundedTauEval :=
  evalTau precision tau3510 contact3510 logTwoBall

theorem center_sq3510 : (center3510.re : ℝ)^2 +
    (center3510.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3510]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3510 : work3510.theta.ok = true ∧
    work3510.jac.invOK = true ∧ acceptsUnitSq work3510.out = true := by decide +kernel

def cell3510 : CellCertificate where
  tauBall := tau3510
  contactCenter := center3510
  contactBall := contact3510
  work := work3510
  center_sq := center_sq3510
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3510.1
  jac_ok := checks3510.2.1
  accepted := checks3510.2.2

def tau3511 : RatBall :=
  ⟨⟨-1/128, 251/640⟩, 3/1280⟩
def center3511 : GaussianRat :=
  ⟨-3221293/500000000, 287852971/1000000000⟩
def contact3511 : RatBall := localContactBall tau3511 center3511
def work3511 : RoundedTauEval :=
  evalTau precision tau3511 contact3511 logTwoBall

theorem center_sq3511 : (center3511.re : ℝ)^2 +
    (center3511.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3511]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3511 : work3511.theta.ok = true ∧
    work3511.jac.invOK = true ∧ acceptsUnitSq work3511.out = true := by decide +kernel

def cell3511 : CellCertificate where
  tauBall := tau3511
  contactCenter := center3511
  contactBall := contact3511
  work := work3511
  center_sq := center_sq3511
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3511.1
  jac_ok := checks3511.2.1
  accepted := checks3511.2.2

def cells : List CellCertificate := [cell3504, cell3505, cell3506, cell3507, cell3508, cell3509, cell3510, cell3511]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438


