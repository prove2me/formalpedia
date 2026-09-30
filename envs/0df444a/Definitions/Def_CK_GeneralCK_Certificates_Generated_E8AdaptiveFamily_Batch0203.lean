-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0203
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0203
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:43:02.274479+00:00
-- url     : https://prove2.me/theorems/02556e59-b9be-4459-9099-687fcff49930
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0203` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0203` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0203` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0203 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0203.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0203 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0203

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1624 : RatBall :=
  ⟨⟨27/320, -109/320⟩, 3/640⟩
def center1624 : GaussianRat :=
  ⟨16551451/250000000, -30513683/125000000⟩
def contact1624 : RatBall := localContactBall tau1624 center1624
def work1624 : RoundedTauEval :=
  evalTau precision tau1624 contact1624 logTwoBall

theorem center_sq1624 : (center1624.re : ℝ)^2 +
    (center1624.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1624]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1624 : work1624.theta.ok = true ∧
    work1624.jac.invOK = true ∧ acceptsUnitSq work1624.out = true := by decide +kernel

def cell1624 : CellCertificate where
  tauBall := tau1624
  contactCenter := center1624
  contactBall := contact1624
  work := work1624
  center_sq := center_sq1624
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1624.1
  jac_ok := checks1624.2.1
  accepted := checks1624.2.2

def tau1625 : RatBall :=
  ⟨⟨29/320, -111/320⟩, 3/640⟩
def center1625 : GaussianRat :=
  ⟨7141811/100000000, -9945447/40000000⟩
def contact1625 : RatBall := localContactBall tau1625 center1625
def work1625 : RoundedTauEval :=
  evalTau precision tau1625 contact1625 logTwoBall

theorem center_sq1625 : (center1625.re : ℝ)^2 +
    (center1625.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1625]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1625 : work1625.theta.ok = true ∧
    work1625.jac.invOK = true ∧ acceptsUnitSq work1625.out = true := by decide +kernel

def cell1625 : CellCertificate where
  tauBall := tau1625
  contactCenter := center1625
  contactBall := contact1625
  work := work1625
  center_sq := center_sq1625
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1625.1
  jac_ok := checks1625.2.1
  accepted := checks1625.2.2

def tau1626 : RatBall :=
  ⟨⟨31/320, -111/320⟩, 3/640⟩
def center1626 : GaussianRat :=
  ⟨76289393/1000000000, -248265049/1000000000⟩
def contact1626 : RatBall := localContactBall tau1626 center1626
def work1626 : RoundedTauEval :=
  evalTau precision tau1626 contact1626 logTwoBall

theorem center_sq1626 : (center1626.re : ℝ)^2 +
    (center1626.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1626]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1626 : work1626.theta.ok = true ∧
    work1626.jac.invOK = true ∧ acceptsUnitSq work1626.out = true := by decide +kernel

def cell1626 : CellCertificate where
  tauBall := tau1626
  contactCenter := center1626
  contactBall := contact1626
  work := work1626
  center_sq := center_sq1626
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1626.1
  jac_ok := checks1626.2.1
  accepted := checks1626.2.2

def tau1627 : RatBall :=
  ⟨⟨29/320, -109/320⟩, 3/640⟩
def center1627 : GaussianRat :=
  ⟨17765923/250000000, -243771477/1000000000⟩
def contact1627 : RatBall := localContactBall tau1627 center1627
def work1627 : RoundedTauEval :=
  evalTau precision tau1627 contact1627 logTwoBall

theorem center_sq1627 : (center1627.re : ℝ)^2 +
    (center1627.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1627]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1627 : work1627.theta.ok = true ∧
    work1627.jac.invOK = true ∧ acceptsUnitSq work1627.out = true := by decide +kernel

def cell1627 : CellCertificate where
  tauBall := tau1627
  contactCenter := center1627
  contactBall := contact1627
  work := work1627
  center_sq := center_sq1627
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1627.1
  jac_ok := checks1627.2.1
  accepted := checks1627.2.2

def tau1628 : RatBall :=
  ⟨⟨31/320, -109/320⟩, 3/640⟩
def center1628 : GaussianRat :=
  ⟨75911827/1000000000, -121705269/500000000⟩
def contact1628 : RatBall := localContactBall tau1628 center1628
def work1628 : RoundedTauEval :=
  evalTau precision tau1628 contact1628 logTwoBall

theorem center_sq1628 : (center1628.re : ℝ)^2 +
    (center1628.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1628]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1628 : work1628.theta.ok = true ∧
    work1628.jac.invOK = true ∧ acceptsUnitSq work1628.out = true := by decide +kernel

def cell1628 : CellCertificate where
  tauBall := tau1628
  contactCenter := center1628
  contactBall := contact1628
  work := work1628
  center_sq := center_sq1628
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1628.1
  jac_ok := checks1628.2.1
  accepted := checks1628.2.2

def tau1629 : RatBall :=
  ⟨⟨33/320, -117/320⟩, 3/640⟩
def center1629 : GaussianRat :=
  ⟨1648401/20000000, -65635667/250000000⟩
def contact1629 : RatBall := localContactBall tau1629 center1629
def work1629 : RoundedTauEval :=
  evalTau precision tau1629 contact1629 logTwoBall

theorem center_sq1629 : (center1629.re : ℝ)^2 +
    (center1629.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1629]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1629 : work1629.theta.ok = true ∧
    work1629.jac.invOK = true ∧ acceptsUnitSq work1629.out = true := by decide +kernel

def cell1629 : CellCertificate where
  tauBall := tau1629
  contactCenter := center1629
  contactBall := contact1629
  work := work1629
  center_sq := center_sq1629
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1629.1
  jac_ok := checks1629.2.1
  accepted := checks1629.2.2

def tau1630 : RatBall :=
  ⟨⟨7/64, -117/320⟩, 3/640⟩
def center1630 : GaussianRat :=
  ⟨43670547/500000000, -65522293/250000000⟩
def contact1630 : RatBall := localContactBall tau1630 center1630
def work1630 : RoundedTauEval :=
  evalTau precision tau1630 contact1630 logTwoBall

theorem center_sq1630 : (center1630.re : ℝ)^2 +
    (center1630.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1630]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1630 : work1630.theta.ok = true ∧
    work1630.jac.invOK = true ∧ acceptsUnitSq work1630.out = true := by decide +kernel

def cell1630 : CellCertificate where
  tauBall := tau1630
  contactCenter := center1630
  contactBall := contact1630
  work := work1630
  center_sq := center_sq1630
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1630.1
  jac_ok := checks1630.2.1
  accepted := checks1630.2.2

def tau1631 : RatBall :=
  ⟨⟨37/320, -117/320⟩, 3/640⟩
def center1631 : GaussianRat :=
  ⟨46124689/500000000, -261610997/1000000000⟩
def contact1631 : RatBall := localContactBall tau1631 center1631
def work1631 : RoundedTauEval :=
  evalTau precision tau1631 contact1631 logTwoBall

theorem center_sq1631 : (center1631.re : ℝ)^2 +
    (center1631.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1631]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1631 : work1631.theta.ok = true ∧
    work1631.jac.invOK = true ∧ acceptsUnitSq work1631.out = true := by decide +kernel

def cell1631 : CellCertificate where
  tauBall := tau1631
  contactCenter := center1631
  contactBall := contact1631
  work := work1631
  center_sq := center_sq1631
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1631.1
  jac_ok := checks1631.2.1
  accepted := checks1631.2.2

def cells : List CellCertificate := [cell1624, cell1625, cell1626, cell1627, cell1628, cell1629, cell1630, cell1631]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0203

end


