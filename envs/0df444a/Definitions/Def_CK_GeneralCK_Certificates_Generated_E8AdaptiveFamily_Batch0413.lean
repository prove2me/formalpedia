-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0413
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0413
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:01:06.592187+00:00
-- url     : https://prove2.me/theorems/d35bbfa4-9efc-45e5-ac4a-829e2e2bec09
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0413.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0413_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3308 : RoundedTauEval :=
  evalTau precision tau3308 contact3308 logTwoBall

theorem center_sq3308 : (center3308.re : ℝ)^2 +
    (center3308.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3308]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3308 : work3308.theta.ok = true ∧
    work3308.jac.invOK = true ∧ acceptsUnitSq work3308.out = true := by decide +kernel

def cell3308 : CellCertificate where
  tauBall := tau3308
  contactCenter := center3308
  contactBall := contact3308
  work := work3308
  center_sq := center_sq3308
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3308.1
  jac_ok := checks3308.2.1
  accepted := checks3308.2.2

def tau3309 : RatBall :=
  ⟨⟨-83/640, 239/640⟩, 3/1280⟩
def center3309 : GaussianRat :=
  ⟨-103935163/1000000000, 66638159/250000000⟩
def contact3309 : RatBall := localContactBall tau3309 center3309
def work3309 : RoundedTauEval :=
  evalTau precision tau3309 contact3309 logTwoBall

theorem center_sq3309 : (center3309.re : ℝ)^2 +
    (center3309.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3309]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3309 : work3309.theta.ok = true ∧
    work3309.jac.invOK = true ∧ acceptsUnitSq work3309.out = true := by decide +kernel

def cell3309 : CellCertificate where
  tauBall := tau3309
  contactCenter := center3309
  contactBall := contact3309
  work := work3309
  center_sq := center_sq3309
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3309.1
  jac_ok := checks3309.2.1
  accepted := checks3309.2.2

def tau3310 : RatBall :=
  ⟨⟨-81/640, 239/640⟩, 3/1280⟩
def center3310 : GaussianRat :=
  ⟨-50741661/500000000, 53366229/200000000⟩
def contact3310 : RatBall := localContactBall tau3310 center3310
def work3310 : RoundedTauEval :=
  evalTau precision tau3310 contact3310 logTwoBall

theorem center_sq3310 : (center3310.re : ℝ)^2 +
    (center3310.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3310]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3310 : work3310.theta.ok = true ∧
    work3310.jac.invOK = true ∧ acceptsUnitSq work3310.out = true := by decide +kernel

def cell3310 : CellCertificate where
  tauBall := tau3310
  contactCenter := center3310
  contactBall := contact3310
  work := work3310
  center_sq := center_sq3310
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3310.1
  jac_ok := checks3310.2.1
  accepted := checks3310.2.2

def tau3311 : RatBall :=
  ⟨⟨-79/640, 237/640⟩, 3/1280⟩
def center3311 : GaussianRat :=
  ⟨-98760267/1000000000, 132324589/500000000⟩
def contact3311 : RatBall := localContactBall tau3311 center3311
def work3311 : RoundedTauEval :=
  evalTau precision tau3311 contact3311 logTwoBall

theorem center_sq3311 : (center3311.re : ℝ)^2 +
    (center3311.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3311]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3311 : work3311.theta.ok = true ∧
    work3311.jac.invOK = true ∧ acceptsUnitSq work3311.out = true := by decide +kernel

def cell3311 : CellCertificate where
  tauBall := tau3311
  contactCenter := center3311
  contactBall := contact3311
  work := work3311
  center_sq := center_sq3311
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3311.1
  jac_ok := checks3311.2.1
  accepted := checks3311.2.2

def cells : List CellCertificate := [cell3304, cell3305, cell3306, cell3307, cell3308, cell3309, cell3310, cell3311]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413


