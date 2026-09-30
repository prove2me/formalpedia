-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0426
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0426
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:19:35.768846+00:00
-- url     : https://prove2.me/theorems/ae4c523f-04b0-4505-adf6-02e1a8d617b0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0426.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0426_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3412 : work3412.theta.ok = true ∧
    work3412.jac.invOK = true ∧ acceptsUnitSq work3412.out = true := by decide +kernel

def cell3412 : CellCertificate where
  tauBall := tau3412
  contactCenter := center3412
  contactBall := contact3412
  work := work3412
  center_sq := center_sq3412
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3412.1
  jac_ok := checks3412.2.1
  accepted := checks3412.2.2

def tau3413 : RatBall :=
  ⟨⟨-43/640, 49/128⟩, 3/1280⟩
def center3413 : GaussianRat :=
  ⟨-6843329/125000000, 556939/2000000⟩
def contact3413 : RatBall := localContactBall tau3413 center3413
def work3413 : RoundedTauEval :=
  evalTau precision tau3413 contact3413 logTwoBall

theorem center_sq3413 : (center3413.re : ℝ)^2 +
    (center3413.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3413]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3413 : work3413.theta.ok = true ∧
    work3413.jac.invOK = true ∧ acceptsUnitSq work3413.out = true := by decide +kernel

def cell3413 : CellCertificate where
  tauBall := tau3413
  contactCenter := center3413
  contactBall := contact3413
  work := work3413
  center_sq := center_sq3413
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3413.1
  jac_ok := checks3413.2.1
  accepted := checks3413.2.2

def tau3414 : RatBall :=
  ⟨⟨-41/640, 49/128⟩, 3/1280⟩
def center3414 : GaussianRat :=
  ⟨-13053747/250000000, 34827989/125000000⟩
def contact3414 : RatBall := localContactBall tau3414 center3414
def work3414 : RoundedTauEval :=
  evalTau precision tau3414 contact3414 logTwoBall

theorem center_sq3414 : (center3414.re : ℝ)^2 +
    (center3414.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3414]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3414 : work3414.theta.ok = true ∧
    work3414.jac.invOK = true ∧ acceptsUnitSq work3414.out = true := by decide +kernel

def cell3414 : CellCertificate where
  tauBall := tau3414
  contactCenter := center3414
  contactBall := contact3414
  work := work3414
  center_sq := center_sq3414
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3414.1
  jac_ok := checks3414.2.1
  accepted := checks3414.2.2

def tau3415 : RatBall :=
  ⟨⟨-43/640, 247/640⟩, 3/1280⟩
def center3415 : GaussianRat :=
  ⟨-3431607/62500000, 70250913/250000000⟩
def contact3415 : RatBall := localContactBall tau3415 center3415
def work3415 : RoundedTauEval :=
  evalTau precision tau3415 contact3415 logTwoBall

theorem center_sq3415 : (center3415.re : ℝ)^2 +
    (center3415.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3415]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3415 : work3415.theta.ok = true ∧
    work3415.jac.invOK = true ∧ acceptsUnitSq work3415.out = true := by decide +kernel

def cell3415 : CellCertificate where
  tauBall := tau3415
  contactCenter := center3415
  contactBall := contact3415
  work := work3415
  center_sq := center_sq3415
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3415.1
  jac_ok := checks3415.2.1
  accepted := checks3415.2.2

def cells : List CellCertificate := [cell3408, cell3409, cell3410, cell3411, cell3412, cell3413, cell3414, cell3415]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426


