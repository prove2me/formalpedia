-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0178_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0178_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:44:11.188623+00:00
-- url     : https://prove2.me/theorems/d3de61cd-224a-4791-9cb2-b221acc71103
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0178 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1424 : RatBall :=
  ⟨⟨-43/320, -111/320⟩, 3/640⟩
def center1424 : GaussianRat :=
  ⟨-21054511/200000000, -122778933/500000000⟩
def contact1424 : RatBall := localContactBall tau1424 center1424
def work1424 : RoundedTauEval :=
  evalTau precision tau1424 contact1424 logTwoBall

theorem center_sq1424 : (center1424.re : ℝ)^2 +
    (center1424.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1424]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1424 : work1424.theta.ok = true ∧
    work1424.jac.invOK = true ∧ acceptsUnitSq work1424.out = true := by decide +kernel

def cell1424 : CellCertificate where
  tauBall := tau1424
  contactCenter := center1424
  contactBall := contact1424
  work := work1424
  center_sq := center_sq1424
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1424.1
  jac_ok := checks1424.2.1
  accepted := checks1424.2.2

def tau1425 : RatBall :=
  ⟨⟨-41/320, -111/320⟩, 3/640⟩
def center1425 : GaussianRat :=
  ⟨-100474143/1000000000, -123032409/500000000⟩
def contact1425 : RatBall := localContactBall tau1425 center1425
def work1425 : RoundedTauEval :=
  evalTau precision tau1425 contact1425 logTwoBall

theorem center_sq1425 : (center1425.re : ℝ)^2 +
    (center1425.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1425]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1425 : work1425.theta.ok = true ∧
    work1425.jac.invOK = true ∧ acceptsUnitSq work1425.out = true := by decide +kernel

def cell1425 : CellCertificate where
  tauBall := tau1425
  contactCenter := center1425
  contactBall := contact1425
  work := work1425
  center_sq := center_sq1425
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1425.1
  jac_ok := checks1425.2.1
  accepted := checks1425.2.2

def tau1426 : RatBall :=
  ⟨⟨-43/320, -109/320⟩, 3/640⟩
def center1426 : GaussianRat :=
  ⟨-26190451/250000000, -3762143/15625000⟩
def contact1426 : RatBall := localContactBall tau1426 center1426
def work1426 : RoundedTauEval :=
  evalTau precision tau1426 contact1426 logTwoBall

theorem center_sq1426 : (center1426.re : ℝ)^2 +
    (center1426.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1426]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1426 : work1426.theta.ok = true ∧
    work1426.jac.invOK = true ∧ acceptsUnitSq work1426.out = true := by decide +kernel

def cell1426 : CellCertificate where
  tauBall := tau1426
  contactCenter := center1426
  contactBall := contact1426
  work := work1426
  center_sq := center_sq1426
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1426.1
  jac_ok := checks1426.2.1
  accepted := checks1426.2.2

def tau1427 : RatBall :=
  ⟨⟨-41/320, -109/320⟩, 3/640⟩
def center1427 : GaussianRat :=
  ⟨-6249053/62500000, -241270351/1000000000⟩
def contact1427 : RatBall := localContactBall tau1427 center1427
def work1427 : RoundedTauEval :=
  evalTau precision tau1427 contact1427 logTwoBall

theorem center_sq1427 : (center1427.re : ℝ)^2 +
    (center1427.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1427]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1427 : work1427.theta.ok = true ∧
    work1427.jac.invOK = true ∧ acceptsUnitSq work1427.out = true := by decide +kernel

def cell1427 : CellCertificate where
  tauBall := tau1427
  contactCenter := center1427
  contactBall := contact1427
  work := work1427
  center_sq := center_sq1427
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1427.1
  jac_ok := checks1427.2.1
  accepted := checks1427.2.2

def tau1428 : RatBall :=
  ⟨⟨-47/320, -107/320⟩, 3/640⟩
def center1428 : GaussianRat :=
  ⟨-56867911/500000000, -234996813/1000000000⟩
def contact1428 : RatBall := localContactBall tau1428 center1428
def work1428 : RoundedTauEval :=
  evalTau precision tau1428 contact1428 logTwoBall

theorem center_sq1428 : (center1428.re : ℝ)^2 +
    (center1428.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1428]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1428 : work1428.theta.ok = true ∧
    work1428.jac.invOK = true ∧ acceptsUnitSq work1428.out = true := by decide +kernel

def cell1428 : CellCertificate where
  tauBall := tau1428
  contactCenter := center1428
  contactBall := contact1428
  work := work1428
  center_sq := center_sq1428
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1428.1
  jac_ok := checks1428.2.1
  accepted := checks1428.2.2

def tau1429 : RatBall :=
  ⟨⟨-9/64, -107/320⟩, 3/640⟩
def center1429 : GaussianRat :=
  ⟨-109007417/1000000000, -235517221/1000000000⟩
def contact1429 : RatBall := localContactBall tau1429 center1429
def work1429 : RoundedTauEval :=
  evalTau precision tau1429 contact1429 logTwoBall

theorem center_sq1429 : (center1429.re : ℝ)^2 +
    (center1429.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1429]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1429 : work1429.theta.ok = true ∧
    work1429.jac.invOK = true ∧ acceptsUnitSq work1429.out = true := by decide +kernel

def cell1429 : CellCertificate where
  tauBall := tau1429
  contactCenter := center1429
  contactBall := contact1429
  work := work1429
  center_sq := center_sq1429
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1429.1
  jac_ok := checks1429.2.1
  accepted := checks1429.2.2

def tau1430 : RatBall :=
  ⟨⟨-47/320, -21/64⟩, 3/640⟩
def center1430 : GaussianRat :=
  ⟨-22642537/200000000, -230285467/1000000000⟩
def contact1430 : RatBall := localContactBall tau1430 center1430
def work1430 : RoundedTauEval :=
  evalTau precision tau1430 contact1430 logTwoBall

theorem center_sq1430 : (center1430.re : ℝ)^2 +
    (center1430.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1430]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178


