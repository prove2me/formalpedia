-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0432
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0432
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:24:11.905287+00:00
-- url     : https://prove2.me/theorems/8619a86d-41fc-49ff-9dec-32776f918da7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0432.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0432_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center3462 : GaussianRat :=
  ⟨-4984851/125000000, 286946953/1000000000⟩
def contact3462 : RatBall := localContactBall tau3462 center3462
def work3462 : RoundedTauEval :=
  evalTau precision tau3462 contact3462 logTwoBall

theorem center_sq3462 : (center3462.re : ℝ)^2 +
    (center3462.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3462]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3462 : work3462.theta.ok = true ∧
    work3462.jac.invOK = true ∧ acceptsUnitSq work3462.out = true := by decide +kernel

def cell3462 : CellCertificate where
  tauBall := tau3462
  contactCenter := center3462
  contactBall := contact3462
  work := work3462
  center_sq := center_sq3462
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3462.1
  jac_ok := checks3462.2.1
  accepted := checks3462.2.2

def tau3463 : RatBall :=
  ⟨⟨-29/640, 251/640⟩, 3/1280⟩
def center3463 : GaussianRat :=
  ⟨-1865689/50000000, 287062723/1000000000⟩
def contact3463 : RatBall := localContactBall tau3463 center3463
def work3463 : RoundedTauEval :=
  evalTau precision tau3463 contact3463 logTwoBall

theorem center_sq3463 : (center3463.re : ℝ)^2 +
    (center3463.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3463]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3463 : work3463.theta.ok = true ∧
    work3463.jac.invOK = true ∧ acceptsUnitSq work3463.out = true := by decide +kernel

def cell3463 : CellCertificate where
  tauBall := tau3463
  contactCenter := center3463
  contactBall := contact3463
  work := work3463
  center_sq := center_sq3463
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3463.1
  jac_ok := checks3463.2.1
  accepted := checks3463.2.2

def cells : List CellCertificate := [cell3456, cell3457, cell3458, cell3459, cell3460, cell3461, cell3462, cell3463]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432


