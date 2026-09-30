-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0428
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0428
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:33:58.794995+00:00
-- url     : https://prove2.me/theorems/6803abea-d828-4c2a-8441-2092b0b192bb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0428.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0428_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3428 : work3428.theta.ok = true ∧
    work3428.jac.invOK = true ∧ acceptsUnitSq work3428.out = true := by decide +kernel

def cell3428 : CellCertificate where
  tauBall := tau3428
  contactCenter := center3428
  contactBall := contact3428
  work := work3428
  center_sq := center_sq3428
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3428.1
  jac_ok := checks3428.2.1
  accepted := checks3428.2.2

def tau3429 : RatBall :=
  ⟨⟨-43/640, 249/640⟩, 3/1280⟩
def center3429 : GaussianRat :=
  ⟨-13766751/250000000, 141772517/500000000⟩
def contact3429 : RatBall := localContactBall tau3429 center3429
def work3429 : RoundedTauEval :=
  evalTau precision tau3429 contact3429 logTwoBall

theorem center_sq3429 : (center3429.re : ℝ)^2 +
    (center3429.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3429]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3429 : work3429.theta.ok = true ∧
    work3429.jac.invOK = true ∧ acceptsUnitSq work3429.out = true := by decide +kernel

def cell3429 : CellCertificate where
  tauBall := tau3429
  contactCenter := center3429
  contactBall := contact3429
  work := work3429
  center_sq := center_sq3429
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3429.1
  jac_ok := checks3429.2.1
  accepted := checks3429.2.2

def tau3430 : RatBall :=
  ⟨⟨-41/640, 249/640⟩, 3/1280⟩
def center3430 : GaussianRat :=
  ⟨-13130217/250000000, 283703773/1000000000⟩
def contact3430 : RatBall := localContactBall tau3430 center3430
def work3430 : RoundedTauEval :=
  evalTau precision tau3430 contact3430 logTwoBall

theorem center_sq3430 : (center3430.re : ℝ)^2 +
    (center3430.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3430]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3430 : work3430.theta.ok = true ∧
    work3430.jac.invOK = true ∧ acceptsUnitSq work3430.out = true := by decide +kernel

def cell3430 : CellCertificate where
  tauBall := tau3430
  contactCenter := center3430
  contactBall := contact3430
  work := work3430
  center_sq := center_sq3430
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3430.1
  jac_ok := checks3430.2.1
  accepted := checks3430.2.2

def tau3431 : RatBall :=
  ⟨⟨-43/640, 251/640⟩, 3/1280⟩
def center3431 : GaussianRat :=
  ⟨-2761527/50000000, 286093747/1000000000⟩
def contact3431 : RatBall := localContactBall tau3431 center3431
def work3431 : RoundedTauEval :=
  evalTau precision tau3431 contact3431 logTwoBall

theorem center_sq3431 : (center3431.re : ℝ)^2 +
    (center3431.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3431]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3431 : work3431.theta.ok = true ∧
    work3431.jac.invOK = true ∧ acceptsUnitSq work3431.out = true := by decide +kernel

def cell3431 : CellCertificate where
  tauBall := tau3431
  contactCenter := center3431
  contactBall := contact3431
  work := work3431
  center_sq := center_sq3431
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3431.1
  jac_ok := checks3431.2.1
  accepted := checks3431.2.2

def cells : List CellCertificate := [cell3424, cell3425, cell3426, cell3427, cell3428, cell3429, cell3430, cell3431]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428


