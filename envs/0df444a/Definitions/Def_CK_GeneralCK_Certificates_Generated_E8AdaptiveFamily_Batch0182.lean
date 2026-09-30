-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0182
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0182
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:50:50.901073+00:00
-- url     : https://prove2.me/theorems/f73bc599-4103-49a5-97dd-7d9cfde50773
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0182` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0182` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0182` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0182 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0182.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0182 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0182

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1456 : RatBall :=
  ⟨⟨-29/320, -119/320⟩, 3/640⟩
def center1456 : GaussianRat :=
  ⟨-14587643/200000000, -268337373/1000000000⟩
def contact1456 : RatBall := localContactBall tau1456 center1456
def work1456 : RoundedTauEval :=
  evalTau precision tau1456 contact1456 logTwoBall

theorem center_sq1456 : (center1456.re : ℝ)^2 +
    (center1456.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1456]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1456 : work1456.theta.ok = true ∧
    work1456.jac.invOK = true ∧ acceptsUnitSq work1456.out = true := by decide +kernel

def cell1456 : CellCertificate where
  tauBall := tau1456
  contactCenter := center1456
  contactBall := contact1456
  work := work1456
  center_sq := center_sq1456
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1456.1
  jac_ok := checks1456.2.1
  accepted := checks1456.2.2

def tau1457 : RatBall :=
  ⟨⟨-31/320, -117/320⟩, 3/640⟩
def center1457 : GaussianRat :=
  ⟨-774869/10000000, -65742793/250000000⟩
def contact1457 : RatBall := localContactBall tau1457 center1457
def work1457 : RoundedTauEval :=
  evalTau precision tau1457 contact1457 logTwoBall

theorem center_sq1457 : (center1457.re : ℝ)^2 +
    (center1457.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1457]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1457 : work1457.theta.ok = true ∧
    work1457.jac.invOK = true ∧ acceptsUnitSq work1457.out = true := by decide +kernel

def cell1457 : CellCertificate where
  tauBall := tau1457
  contactCenter := center1457
  contactBall := contact1457
  work := work1457
  center_sq := center_sq1457
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1457.1
  jac_ok := checks1457.2.1
  accepted := checks1457.2.2

def tau1458 : RatBall :=
  ⟨⟨-29/320, -117/320⟩, 3/640⟩
def center1458 : GaussianRat :=
  ⟨-7254231/100000000, -263374389/1000000000⟩
def contact1458 : RatBall := localContactBall tau1458 center1458
def work1458 : RoundedTauEval :=
  evalTau precision tau1458 contact1458 logTwoBall

theorem center_sq1458 : (center1458.re : ℝ)^2 +
    (center1458.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1458]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1458 : work1458.theta.ok = true ∧
    work1458.jac.invOK = true ∧ acceptsUnitSq work1458.out = true := by decide +kernel

def cell1458 : CellCertificate where
  tauBall := tau1458
  contactCenter := center1458
  contactBall := contact1458
  work := work1458
  center_sq := center_sq1458
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1458.1
  jac_ok := checks1458.2.1
  accepted := checks1458.2.2

def tau1459 : RatBall :=
  ⟨⟨-27/320, -119/320⟩, 3/640⟩
def center1459 : GaussianRat :=
  ⟨-33978407/500000000, -67181393/250000000⟩
def contact1459 : RatBall := localContactBall tau1459 center1459
def work1459 : RoundedTauEval :=
  evalTau precision tau1459 contact1459 logTwoBall

theorem center_sq1459 : (center1459.re : ℝ)^2 +
    (center1459.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1459]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1459 : work1459.theta.ok = true ∧
    work1459.jac.invOK = true ∧ acceptsUnitSq work1459.out = true := by decide +kernel

def cell1459 : CellCertificate where
  tauBall := tau1459
  contactCenter := center1459
  contactBall := contact1459
  work := work1459
  center_sq := center_sq1459
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1459.1
  jac_ok := checks1459.2.1
  accepted := checks1459.2.2

def tau1460 : RatBall :=
  ⟨⟨-5/64, -119/320⟩, 3/640⟩
def center1460 : GaussianRat :=
  ⟨-1574127/25000000, -53817447/200000000⟩
def contact1460 : RatBall := localContactBall tau1460 center1460
def work1460 : RoundedTauEval :=
  evalTau precision tau1460 contact1460 logTwoBall

theorem center_sq1460 : (center1460.re : ℝ)^2 +
    (center1460.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1460]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1460 : work1460.theta.ok = true ∧
    work1460.jac.invOK = true ∧ acceptsUnitSq work1460.out = true := by decide +kernel

def cell1460 : CellCertificate where
  tauBall := tau1460
  contactCenter := center1460
  contactBall := contact1460
  work := work1460
  center_sq := center_sq1460
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1460.1
  jac_ok := checks1460.2.1
  accepted := checks1460.2.2

def tau1461 : RatBall :=
  ⟨⟨-27/320, -117/320⟩, 3/640⟩
def center1461 : GaussianRat :=
  ⟨-844837/12500000, -131876019/500000000⟩
def contact1461 : RatBall := localContactBall tau1461 center1461
def work1461 : RoundedTauEval :=
  evalTau precision tau1461 contact1461 logTwoBall

theorem center_sq1461 : (center1461.re : ℝ)^2 +
    (center1461.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1461]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1461 : work1461.theta.ok = true ∧
    work1461.jac.invOK = true ∧ acceptsUnitSq work1461.out = true := by decide +kernel

def cell1461 : CellCertificate where
  tauBall := tau1461
  contactCenter := center1461
  contactBall := contact1461
  work := work1461
  center_sq := center_sq1461
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1461.1
  jac_ok := checks1461.2.1
  accepted := checks1461.2.2

def tau1462 : RatBall :=
  ⟨⟨-5/64, -117/320⟩, 3/640⟩
def center1462 : GaussianRat :=
  ⟨-3131077/50000000, -66025963/250000000⟩
def contact1462 : RatBall := localContactBall tau1462 center1462
def work1462 : RoundedTauEval :=
  evalTau precision tau1462 contact1462 logTwoBall

theorem center_sq1462 : (center1462.re : ℝ)^2 +
    (center1462.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1462]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1462 : work1462.theta.ok = true ∧
    work1462.jac.invOK = true ∧ acceptsUnitSq work1462.out = true := by decide +kernel

def cell1462 : CellCertificate where
  tauBall := tau1462
  contactCenter := center1462
  contactBall := contact1462
  work := work1462
  center_sq := center_sq1462
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1462.1
  jac_ok := checks1462.2.1
  accepted := checks1462.2.2

def tau1463 : RatBall :=
  ⟨⟨-31/320, -23/64⟩, 3/640⟩
def center1463 : GaussianRat :=
  ⟨-77076663/1000000000, -258044723/1000000000⟩
def contact1463 : RatBall := localContactBall tau1463 center1463
def work1463 : RoundedTauEval :=
  evalTau precision tau1463 contact1463 logTwoBall

theorem center_sq1463 : (center1463.re : ℝ)^2 +
    (center1463.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1463]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1463 : work1463.theta.ok = true ∧
    work1463.jac.invOK = true ∧ acceptsUnitSq work1463.out = true := by decide +kernel

def cell1463 : CellCertificate where
  tauBall := tau1463
  contactCenter := center1463
  contactBall := contact1463
  work := work1463
  center_sq := center_sq1463
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1463.1
  jac_ok := checks1463.2.1
  accepted := checks1463.2.2

def cells : List CellCertificate := [cell1456, cell1457, cell1458, cell1459, cell1460, cell1461, cell1462, cell1463]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0182

end


