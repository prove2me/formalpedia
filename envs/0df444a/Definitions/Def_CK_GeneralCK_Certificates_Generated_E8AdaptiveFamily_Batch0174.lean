-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0174
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0174
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:44:31.346688+00:00
-- url     : https://prove2.me/theorems/fcf1e0e0-8343-4249-8103-130b2375013e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0174` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0174` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0174` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0174 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0174.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0174 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0174

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1392 : RatBall :=
  ⟨⟨-51/320, -107/320⟩, 3/640⟩
def center1392 : GaussianRat :=
  ⟨-24629661/200000000, -233896771/1000000000⟩
def contact1392 : RatBall := localContactBall tau1392 center1392
def work1392 : RoundedTauEval :=
  evalTau precision tau1392 contact1392 logTwoBall

theorem center_sq1392 : (center1392.re : ℝ)^2 +
    (center1392.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1392]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1392 : work1392.theta.ok = true ∧
    work1392.jac.invOK = true ∧ acceptsUnitSq work1392.out = true := by decide +kernel

def cell1392 : CellCertificate where
  tauBall := tau1392
  contactCenter := center1392
  contactBall := contact1392
  work := work1392
  center_sq := center_sq1392
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1392.1
  jac_ok := checks1392.2.1
  accepted := checks1392.2.2

def tau1393 : RatBall :=
  ⟨⟨-49/320, -107/320⟩, 3/640⟩
def center1393 : GaussianRat :=
  ⟨-5922481/50000000, -234456553/1000000000⟩
def contact1393 : RatBall := localContactBall tau1393 center1393
def work1393 : RoundedTauEval :=
  evalTau precision tau1393 contact1393 logTwoBall

theorem center_sq1393 : (center1393.re : ℝ)^2 +
    (center1393.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1393]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1393 : work1393.theta.ok = true ∧
    work1393.jac.invOK = true ∧ acceptsUnitSq work1393.out = true := by decide +kernel

def cell1393 : CellCertificate where
  tauBall := tau1393
  contactCenter := center1393
  contactBall := contact1393
  work := work1393
  center_sq := center_sq1393
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1393.1
  jac_ok := checks1393.2.1
  accepted := checks1393.2.2

def tau1394 : RatBall :=
  ⟨⟨-51/320, -21/64⟩, 3/640⟩
def center1394 : GaussianRat :=
  ⟨-122586619/1000000000, -229215321/1000000000⟩
def contact1394 : RatBall := localContactBall tau1394 center1394
def work1394 : RoundedTauEval :=
  evalTau precision tau1394 contact1394 logTwoBall

theorem center_sq1394 : (center1394.re : ℝ)^2 +
    (center1394.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1394]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1394 : work1394.theta.ok = true ∧
    work1394.jac.invOK = true ∧ acceptsUnitSq work1394.out = true := by decide +kernel

def cell1394 : CellCertificate where
  tauBall := tau1394
  contactCenter := center1394
  contactBall := contact1394
  work := work1394
  center_sq := center_sq1394
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1394.1
  jac_ok := checks1394.2.1
  accepted := checks1394.2.2

def tau1395 : RatBall :=
  ⟨⟨-49/320, -21/64⟩, 3/640⟩
def center1395 : GaussianRat :=
  ⟨-58953523/500000000, -57439977/250000000⟩
def contact1395 : RatBall := localContactBall tau1395 center1395
def work1395 : RoundedTauEval :=
  evalTau precision tau1395 contact1395 logTwoBall

theorem center_sq1395 : (center1395.re : ℝ)^2 +
    (center1395.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1395]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1395 : work1395.theta.ok = true ∧
    work1395.jac.invOK = true ∧ acceptsUnitSq work1395.out = true := by decide +kernel

def cell1395 : CellCertificate where
  tauBall := tau1395
  contactCenter := center1395
  contactBall := contact1395
  work := work1395
  center_sq := center_sq1395
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1395.1
  jac_ok := checks1395.2.1
  accepted := checks1395.2.2

def tau1396 : RatBall :=
  ⟨⟨-63/320, -103/320⟩, 3/640⟩
def center1396 : GaussianRat :=
  ⟨-74838049/500000000, -221002847/1000000000⟩
def contact1396 : RatBall := localContactBall tau1396 center1396
def work1396 : RoundedTauEval :=
  evalTau precision tau1396 contact1396 logTwoBall

theorem center_sq1396 : (center1396.re : ℝ)^2 +
    (center1396.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1396]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1396 : work1396.theta.ok = true ∧
    work1396.jac.invOK = true ∧ acceptsUnitSq work1396.out = true := by decide +kernel

def cell1396 : CellCertificate where
  tauBall := tau1396
  contactCenter := center1396
  contactBall := contact1396
  work := work1396
  center_sq := center_sq1396
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1396.1
  jac_ok := checks1396.2.1
  accepted := checks1396.2.2

def tau1397 : RatBall :=
  ⟨⟨-61/320, -103/320⟩, 3/640⟩
def center1397 : GaussianRat :=
  ⟨-5804463/40000000, -221637027/1000000000⟩
def contact1397 : RatBall := localContactBall tau1397 center1397
def work1397 : RoundedTauEval :=
  evalTau precision tau1397 contact1397 logTwoBall

theorem center_sq1397 : (center1397.re : ℝ)^2 +
    (center1397.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1397]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1397 : work1397.theta.ok = true ∧
    work1397.jac.invOK = true ∧ acceptsUnitSq work1397.out = true := by decide +kernel

def cell1397 : CellCertificate where
  tauBall := tau1397
  contactCenter := center1397
  contactBall := contact1397
  work := work1397
  center_sq := center_sq1397
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1397.1
  jac_ok := checks1397.2.1
  accepted := checks1397.2.2

def tau1398 : RatBall :=
  ⟨⟨-63/320, -101/320⟩, 3/640⟩
def center1398 : GaussianRat :=
  ⟨-74521233/500000000, -108227539/500000000⟩
def contact1398 : RatBall := localContactBall tau1398 center1398
def work1398 : RoundedTauEval :=
  evalTau precision tau1398 contact1398 logTwoBall

theorem center_sq1398 : (center1398.re : ℝ)^2 +
    (center1398.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1398]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1398 : work1398.theta.ok = true ∧
    work1398.jac.invOK = true ∧ acceptsUnitSq work1398.out = true := by decide +kernel

def cell1398 : CellCertificate where
  tauBall := tau1398
  contactCenter := center1398
  contactBall := contact1398
  work := work1398
  center_sq := center_sq1398
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1398.1
  jac_ok := checks1398.2.1
  accepted := checks1398.2.2

def tau1399 : RatBall :=
  ⟨⟨-61/320, -101/320⟩, 3/640⟩
def center1399 : GaussianRat :=
  ⟨-7224707/50000000, -217072079/1000000000⟩
def contact1399 : RatBall := localContactBall tau1399 center1399
def work1399 : RoundedTauEval :=
  evalTau precision tau1399 contact1399 logTwoBall

theorem center_sq1399 : (center1399.re : ℝ)^2 +
    (center1399.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1399]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1399 : work1399.theta.ok = true ∧
    work1399.jac.invOK = true ∧ acceptsUnitSq work1399.out = true := by decide +kernel

def cell1399 : CellCertificate where
  tauBall := tau1399
  contactCenter := center1399
  contactBall := contact1399
  work := work1399
  center_sq := center_sq1399
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1399.1
  jac_ok := checks1399.2.1
  accepted := checks1399.2.2

def cells : List CellCertificate := [cell1392, cell1393, cell1394, cell1395, cell1396, cell1397, cell1398, cell1399]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0174

end


