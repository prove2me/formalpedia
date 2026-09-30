-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0172_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0172_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:14:09.112097+00:00
-- url     : https://prove2.me/theorems/b0704e8e-4be1-473f-9ffd-d0ce9e0008a8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0172 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1376 : RatBall :=
  ⟨⟨-59/320, -107/320⟩, 3/640⟩
def center1376 : GaussianRat :=
  ⟨-141782257/1000000000, -231469249/1000000000⟩
def contact1376 : RatBall := localContactBall tau1376 center1376
def work1376 : RoundedTauEval :=
  evalTau precision tau1376 contact1376 logTwoBall

theorem center_sq1376 : (center1376.re : ℝ)^2 +
    (center1376.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1376]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1376 : work1376.theta.ok = true ∧
    work1376.jac.invOK = true ∧ acceptsUnitSq work1376.out = true := by decide +kernel

def cell1376 : CellCertificate where
  tauBall := tau1376
  contactCenter := center1376
  contactBall := contact1376
  work := work1376
  center_sq := center_sq1376
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1376.1
  jac_ok := checks1376.2.1
  accepted := checks1376.2.2

def tau1377 : RatBall :=
  ⟨⟨-57/320, -107/320⟩, 3/640⟩
def center1377 : GaussianRat :=
  ⟨-6857441/50000000, -46420737/200000000⟩
def contact1377 : RatBall := localContactBall tau1377 center1377
def work1377 : RoundedTauEval :=
  evalTau precision tau1377 contact1377 logTwoBall

theorem center_sq1377 : (center1377.re : ℝ)^2 +
    (center1377.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1377]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1377 : work1377.theta.ok = true ∧
    work1377.jac.invOK = true ∧ acceptsUnitSq work1377.out = true := by decide +kernel

def cell1377 : CellCertificate where
  tauBall := tau1377
  contactCenter := center1377
  contactBall := contact1377
  work := work1377
  center_sq := center_sq1377
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1377.1
  jac_ok := checks1377.2.1
  accepted := checks1377.2.2

def tau1378 : RatBall :=
  ⟨⟨-59/320, -21/64⟩, 3/640⟩
def center1378 : GaussianRat :=
  ⟨-70573769/500000000, -113426637/500000000⟩
def contact1378 : RatBall := localContactBall tau1378 center1378
def work1378 : RoundedTauEval :=
  evalTau precision tau1378 contact1378 logTwoBall

theorem center_sq1378 : (center1378.re : ℝ)^2 +
    (center1378.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1378]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1378 : work1378.theta.ok = true ∧
    work1378.jac.invOK = true ∧ acceptsUnitSq work1378.out = true := by decide +kernel

def cell1378 : CellCertificate where
  tauBall := tau1378
  contactCenter := center1378
  contactBall := contact1378
  work := work1378
  center_sq := center_sq1378
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1378.1
  jac_ok := checks1378.2.1
  accepted := checks1378.2.2

def tau1379 : RatBall :=
  ⟨⟨-57/320, -21/64⟩, 3/640⟩
def center1379 : GaussianRat :=
  ⟨-136531833/1000000000, -227470663/1000000000⟩
def contact1379 : RatBall := localContactBall tau1379 center1379
def work1379 : RoundedTauEval :=
  evalTau precision tau1379 contact1379 logTwoBall

theorem center_sq1379 : (center1379.re : ℝ)^2 +
    (center1379.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1379]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1379 : work1379.theta.ok = true ∧
    work1379.jac.invOK = true ∧ acceptsUnitSq work1379.out = true := by decide +kernel

def cell1379 : CellCertificate where
  tauBall := tau1379
  contactCenter := center1379
  contactBall := contact1379
  work := work1379
  center_sq := center_sq1379
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1379.1
  jac_ok := checks1379.2.1
  accepted := checks1379.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172


