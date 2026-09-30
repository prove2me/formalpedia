-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0434
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0434
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:27:21.090535+00:00
-- url     : https://prove2.me/theorems/5349826a-4f14-4280-80c4-5aec2495c0f8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0434.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0434_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3477 : work3477.theta.ok = true ∧
    work3477.jac.invOK = true ∧ acceptsUnitSq work3477.out = true := by decide +kernel

def cell3477 : CellCertificate where
  tauBall := tau3477
  contactCenter := center3477
  contactBall := contact3477
  work := work3477
  center_sq := center_sq3477
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3477.1
  jac_ok := checks3477.2.1
  accepted := checks3477.2.2

def tau3478 : RatBall :=
  ⟨⟨-23/640, 251/640⟩, 3/1280⟩
def center3478 : GaussianRat :=
  ⟨-14804897/500000000, 8980133/31250000⟩
def contact3478 : RatBall := localContactBall tau3478 center3478
def work3478 : RoundedTauEval :=
  evalTau precision tau3478 contact3478 logTwoBall

theorem center_sq3478 : (center3478.re : ℝ)^2 +
    (center3478.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3478]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3478 : work3478.theta.ok = true ∧
    work3478.jac.invOK = true ∧ acceptsUnitSq work3478.out = true := by decide +kernel

def cell3478 : CellCertificate where
  tauBall := tau3478
  contactCenter := center3478
  contactBall := contact3478
  work := work3478
  center_sq := center_sq3478
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3478.1
  jac_ok := checks3478.2.1
  accepted := checks3478.2.2

def tau3479 : RatBall :=
  ⟨⟨-21/640, 251/640⟩, 3/1280⟩
def center3479 : GaussianRat :=
  ⟨-1689949/62500000, 143724721/500000000⟩
def contact3479 : RatBall := localContactBall tau3479 center3479
def work3479 : RoundedTauEval :=
  evalTau precision tau3479 contact3479 logTwoBall

theorem center_sq3479 : (center3479.re : ℝ)^2 +
    (center3479.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3479]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3479 : work3479.theta.ok = true ∧
    work3479.jac.invOK = true ∧ acceptsUnitSq work3479.out = true := by decide +kernel

def cell3479 : CellCertificate where
  tauBall := tau3479
  contactCenter := center3479
  contactBall := contact3479
  work := work3479
  center_sq := center_sq3479
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3479.1
  jac_ok := checks3479.2.1
  accepted := checks3479.2.2

def cells : List CellCertificate := [cell3472, cell3473, cell3474, cell3475, cell3476, cell3477, cell3478, cell3479]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434


