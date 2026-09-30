-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0418
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0418
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:48:50.463212+00:00
-- url     : https://prove2.me/theorems/2d28b2be-ce3c-4a5e-8fa6-ad5ae7cc1733
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0418.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0418_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3348 : (center3348.re : ℝ)^2 +
    (center3348.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3348]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3348 : work3348.theta.ok = true ∧
    work3348.jac.invOK = true ∧ acceptsUnitSq work3348.out = true := by decide +kernel

def cell3348 : CellCertificate where
  tauBall := tau3348
  contactCenter := center3348
  contactBall := contact3348
  work := work3348
  center_sq := center_sq3348
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3348.1
  jac_ok := checks3348.2.1
  accepted := checks3348.2.2

def tau3349 : RatBall :=
  ⟨⟨-67/640, 241/640⟩, 3/1280⟩
def center3349 : GaussianRat :=
  ⟨-84453299/1000000000, 5421753/20000000⟩
def contact3349 : RatBall := localContactBall tau3349 center3349
def work3349 : RoundedTauEval :=
  evalTau precision tau3349 contact3349 logTwoBall

theorem center_sq3349 : (center3349.re : ℝ)^2 +
    (center3349.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3349]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3349 : work3349.theta.ok = true ∧
    work3349.jac.invOK = true ∧ acceptsUnitSq work3349.out = true := by decide +kernel

def cell3349 : CellCertificate where
  tauBall := tau3349
  contactCenter := center3349
  contactBall := contact3349
  work := work3349
  center_sq := center_sq3349
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3349.1
  jac_ok := checks3349.2.1
  accepted := checks3349.2.2

def tau3350 : RatBall :=
  ⟨⟨-13/128, 241/640⟩, 3/1280⟩
def center3350 : GaussianRat :=
  ⟨-40983659/500000000, 135659503/500000000⟩
def contact3350 : RatBall := localContactBall tau3350 center3350
def work3350 : RoundedTauEval :=
  evalTau precision tau3350 contact3350 logTwoBall

theorem center_sq3350 : (center3350.re : ℝ)^2 +
    (center3350.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3350]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3350 : work3350.theta.ok = true ∧
    work3350.jac.invOK = true ∧ acceptsUnitSq work3350.out = true := by decide +kernel

def cell3350 : CellCertificate where
  tauBall := tau3350
  contactCenter := center3350
  contactBall := contact3350
  work := work3350
  center_sq := center_sq3350
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3350.1
  jac_ok := checks3350.2.1
  accepted := checks3350.2.2

def tau3351 : RatBall :=
  ⟨⟨-67/640, 243/640⟩, 3/1280⟩
def center3351 : GaussianRat :=
  ⟨-42344767/500000000, 273575317/1000000000⟩
def contact3351 : RatBall := localContactBall tau3351 center3351
def work3351 : RoundedTauEval :=
  evalTau precision tau3351 contact3351 logTwoBall

theorem center_sq3351 : (center3351.re : ℝ)^2 +
    (center3351.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3351]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3351 : work3351.theta.ok = true ∧
    work3351.jac.invOK = true ∧ acceptsUnitSq work3351.out = true := by decide +kernel

def cell3351 : CellCertificate where
  tauBall := tau3351
  contactCenter := center3351
  contactBall := contact3351
  work := work3351
  center_sq := center_sq3351
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3351.1
  jac_ok := checks3351.2.1
  accepted := checks3351.2.2

def cells : List CellCertificate := [cell3344, cell3345, cell3346, cell3347, cell3348, cell3349, cell3350, cell3351]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418


