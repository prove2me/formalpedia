-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0170
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0170
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:00:27.626918+00:00
-- url     : https://prove2.me/theorems/b5bfc7ce-8fa5-4975-8582-3c72f7ee64a6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0170` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0170` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0170` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0170 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0170.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0170 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0170

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1360 : RatBall :=
  ⟨⟨-39/320, -113/320⟩, 3/640⟩
def center1360 : GaussianRat :=
  ⟨-48071341/500000000, -251379737/1000000000⟩
def contact1360 : RatBall := localContactBall tau1360 center1360
def work1360 : RoundedTauEval :=
  evalTau precision tau1360 contact1360 logTwoBall

theorem center_sq1360 : (center1360.re : ℝ)^2 +
    (center1360.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1360]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1360 : work1360.theta.ok = true ∧
    work1360.jac.invOK = true ∧ acceptsUnitSq work1360.out = true := by decide +kernel

def cell1360 : CellCertificate where
  tauBall := tau1360
  contactCenter := center1360
  contactBall := contact1360
  work := work1360
  center_sq := center_sq1360
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1360.1
  jac_ok := checks1360.2.1
  accepted := checks1360.2.2

def tau1361 : RatBall :=
  ⟨⟨-37/320, -113/320⟩, 3/640⟩
def center1361 : GaussianRat :=
  ⟨-45647467/500000000, -62963873/250000000⟩
def contact1361 : RatBall := localContactBall tau1361 center1361
def work1361 : RoundedTauEval :=
  evalTau precision tau1361 contact1361 logTwoBall

theorem center_sq1361 : (center1361.re : ℝ)^2 +
    (center1361.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1361]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1361 : work1361.theta.ok = true ∧
    work1361.jac.invOK = true ∧ acceptsUnitSq work1361.out = true := by decide +kernel

def cell1361 : CellCertificate where
  tauBall := tau1361
  contactCenter := center1361
  contactBall := contact1361
  work := work1361
  center_sq := center_sq1361
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1361.1
  jac_ok := checks1361.2.1
  accepted := checks1361.2.2

def tau1362 : RatBall :=
  ⟨⟨-7/64, -23/64⟩, 3/640⟩
def center1362 : GaussianRat :=
  ⟨-43440767/500000000, -257186633/1000000000⟩
def contact1362 : RatBall := localContactBall tau1362 center1362
def work1362 : RoundedTauEval :=
  evalTau precision tau1362 contact1362 logTwoBall

theorem center_sq1362 : (center1362.re : ℝ)^2 +
    (center1362.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1362]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1362 : work1362.theta.ok = true ∧
    work1362.jac.invOK = true ∧ acceptsUnitSq work1362.out = true := by decide +kernel

def cell1362 : CellCertificate where
  tauBall := tau1362
  contactCenter := center1362
  contactBall := contact1362
  work := work1362
  center_sq := center_sq1362
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1362.1
  jac_ok := checks1362.2.1
  accepted := checks1362.2.2

def tau1363 : RatBall :=
  ⟨⟨-33/320, -23/64⟩, 3/640⟩
def center1363 : GaussianRat :=
  ⟨-40992501/500000000, -257627847/1000000000⟩
def contact1363 : RatBall := localContactBall tau1363 center1363
def work1363 : RoundedTauEval :=
  evalTau precision tau1363 contact1363 logTwoBall

theorem center_sq1363 : (center1363.re : ℝ)^2 +
    (center1363.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1363]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1363 : work1363.theta.ok = true ∧
    work1363.jac.invOK = true ∧ acceptsUnitSq work1363.out = true := by decide +kernel

def cell1363 : CellCertificate where
  tauBall := tau1363
  contactCenter := center1363
  contactBall := contact1363
  work := work1363
  center_sq := center_sq1363
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1363.1
  jac_ok := checks1363.2.1
  accepted := checks1363.2.2

def tau1364 : RatBall :=
  ⟨⟨-7/64, -113/320⟩, 3/640⟩
def center1364 : GaussianRat :=
  ⟨-86434423/1000000000, -50461627/200000000⟩
def contact1364 : RatBall := localContactBall tau1364 center1364
def work1364 : RoundedTauEval :=
  evalTau precision tau1364 contact1364 logTwoBall

theorem center_sq1364 : (center1364.re : ℝ)^2 +
    (center1364.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1364]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1364 : work1364.theta.ok = true ∧
    work1364.jac.invOK = true ∧ acceptsUnitSq work1364.out = true := by decide +kernel

def cell1364 : CellCertificate where
  tauBall := tau1364
  contactCenter := center1364
  contactBall := contact1364
  work := work1364
  center_sq := center_sq1364
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1364.1
  jac_ok := checks1364.2.1
  accepted := checks1364.2.2

def tau1365 : RatBall :=
  ⟨⟨-33/320, -113/320⟩, 3/640⟩
def center1365 : GaussianRat :=
  ⟨-16312353/200000000, -252737367/1000000000⟩
def contact1365 : RatBall := localContactBall tau1365 center1365
def work1365 : RoundedTauEval :=
  evalTau precision tau1365 contact1365 logTwoBall

theorem center_sq1365 : (center1365.re : ℝ)^2 +
    (center1365.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1365]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1365 : work1365.theta.ok = true ∧
    work1365.jac.invOK = true ∧ acceptsUnitSq work1365.out = true := by decide +kernel

def cell1365 : CellCertificate where
  tauBall := tau1365
  contactCenter := center1365
  contactBall := contact1365
  work := work1365
  center_sq := center_sq1365
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1365.1
  jac_ok := checks1365.2.1
  accepted := checks1365.2.2

def tau1366 : RatBall :=
  ⟨⟨-63/320, -109/320⟩, 3/640⟩
def center1366 : GaussianRat :=
  ⟨-75841877/500000000, -234745077/1000000000⟩
def contact1366 : RatBall := localContactBall tau1366 center1366
def work1366 : RoundedTauEval :=
  evalTau precision tau1366 contact1366 logTwoBall

theorem center_sq1366 : (center1366.re : ℝ)^2 +
    (center1366.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1366]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1366 : work1366.theta.ok = true ∧
    work1366.jac.invOK = true ∧ acceptsUnitSq work1366.out = true := by decide +kernel

def cell1366 : CellCertificate where
  tauBall := tau1366
  contactCenter := center1366
  contactBall := contact1366
  work := work1366
  center_sq := center_sq1366
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1366.1
  jac_ok := checks1366.2.1
  accepted := checks1366.2.2

def tau1367 : RatBall :=
  ⟨⟨-61/320, -109/320⟩, 3/640⟩
def center1367 : GaussianRat :=
  ⟨-147068213/1000000000, -14714559/62500000⟩
def contact1367 : RatBall := localContactBall tau1367 center1367
def work1367 : RoundedTauEval :=
  evalTau precision tau1367 contact1367 logTwoBall

theorem center_sq1367 : (center1367.re : ℝ)^2 +
    (center1367.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1367]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1367 : work1367.theta.ok = true ∧
    work1367.jac.invOK = true ∧ acceptsUnitSq work1367.out = true := by decide +kernel

def cell1367 : CellCertificate where
  tauBall := tau1367
  contactCenter := center1367
  contactBall := contact1367
  work := work1367
  center_sq := center_sq1367
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1367.1
  jac_ok := checks1367.2.1
  accepted := checks1367.2.2

def cells : List CellCertificate := [cell1360, cell1361, cell1362, cell1363, cell1364, cell1365, cell1366, cell1367]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0170

end


