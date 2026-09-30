-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0206
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0206
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:09:05.346482+00:00
-- url     : https://prove2.me/theorems/77b42456-73ea-4212-8643-380b28144919
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0206` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0206` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0206` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0206 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0206.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0206 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0206

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1648 : RatBall :=
  ⟨⟨49/320, -113/320⟩, 3/640⟩
def center1648 : GaussianRat :=
  ⟨120169401/1000000000, -248665661/1000000000⟩
def contact1648 : RatBall := localContactBall tau1648 center1648
def work1648 : RoundedTauEval :=
  evalTau precision tau1648 contact1648 logTwoBall

theorem center_sq1648 : (center1648.re : ℝ)^2 +
    (center1648.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1648]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1648 : work1648.theta.ok = true ∧
    work1648.jac.invOK = true ∧ acceptsUnitSq work1648.out = true := by decide +kernel

def cell1648 : CellCertificate where
  tauBall := tau1648
  contactCenter := center1648
  contactBall := contact1648
  work := work1648
  center_sq := center_sq1648
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1648.1
  jac_ok := checks1648.2.1
  accepted := checks1648.2.2

def tau1649 : RatBall :=
  ⟨⟨51/320, -113/320⟩, 3/640⟩
def center1649 : GaussianRat :=
  ⟨124928411/1000000000, -12402911/50000000⟩
def contact1649 : RatBall := localContactBall tau1649 center1649
def work1649 : RoundedTauEval :=
  evalTau precision tau1649 contact1649 logTwoBall

theorem center_sq1649 : (center1649.re : ℝ)^2 +
    (center1649.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1649]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1649 : work1649.theta.ok = true ∧
    work1649.jac.invOK = true ∧ acceptsUnitSq work1649.out = true := by decide +kernel

def cell1649 : CellCertificate where
  tauBall := tau1649
  contactCenter := center1649
  contactBall := contact1649
  work := work1649
  center_sq := center_sq1649
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1649.1
  jac_ok := checks1649.2.1
  accepted := checks1649.2.2

def tau1650 : RatBall :=
  ⟨⟨53/320, -113/320⟩, 3/640⟩
def center1650 : GaussianRat :=
  ⟨129670733/1000000000, -15464381/62500000⟩
def contact1650 : RatBall := localContactBall tau1650 center1650
def work1650 : RoundedTauEval :=
  evalTau precision tau1650 contact1650 logTwoBall

theorem center_sq1650 : (center1650.re : ℝ)^2 +
    (center1650.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1650]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1650 : work1650.theta.ok = true ∧
    work1650.jac.invOK = true ∧ acceptsUnitSq work1650.out = true := by decide +kernel

def cell1650 : CellCertificate where
  tauBall := tau1650
  contactCenter := center1650
  contactBall := contact1650
  work := work1650
  center_sq := center_sq1650
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1650.1
  jac_ok := checks1650.2.1
  accepted := checks1650.2.2

def tau1651 : RatBall :=
  ⟨⟨33/320, -111/320⟩, 3/640⟩
def center1651 : GaussianRat :=
  ⟨20287513/250000000, -247870587/1000000000⟩
def contact1651 : RatBall := localContactBall tau1651 center1651
def work1651 : RoundedTauEval :=
  evalTau precision tau1651 contact1651 logTwoBall

theorem center_sq1651 : (center1651.re : ℝ)^2 +
    (center1651.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1651]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1651 : work1651.theta.ok = true ∧
    work1651.jac.invOK = true ∧ acceptsUnitSq work1651.out = true := by decide +kernel

def cell1651 : CellCertificate where
  tauBall := tau1651
  contactCenter := center1651
  contactBall := contact1651
  work := work1651
  center_sq := center_sq1651
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1651.1
  jac_ok := checks1651.2.1
  accepted := checks1651.2.2

def tau1652 : RatBall :=
  ⟨⟨7/64, -111/320⟩, 3/640⟩
def center1652 : GaussianRat :=
  ⟨85999463/1000000000, -247453051/1000000000⟩
def contact1652 : RatBall := localContactBall tau1652 center1652
def work1652 : RoundedTauEval :=
  evalTau precision tau1652 contact1652 logTwoBall

theorem center_sq1652 : (center1652.re : ℝ)^2 +
    (center1652.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1652]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1652 : work1652.theta.ok = true ∧
    work1652.jac.invOK = true ∧ acceptsUnitSq work1652.out = true := by decide +kernel

def cell1652 : CellCertificate where
  tauBall := tau1652
  contactCenter := center1652
  contactBall := contact1652
  work := work1652
  center_sq := center_sq1652
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1652.1
  jac_ok := checks1652.2.1
  accepted := checks1652.2.2

def tau1653 : RatBall :=
  ⟨⟨33/320, -109/320⟩, 3/640⟩
def center1653 : GaussianRat :=
  ⟨20187397/250000000, -48605377/200000000⟩
def contact1653 : RatBall := localContactBall tau1653 center1653
def work1653 : RoundedTauEval :=
  evalTau precision tau1653 contact1653 logTwoBall

theorem center_sq1653 : (center1653.re : ℝ)^2 +
    (center1653.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1653]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1653 : work1653.theta.ok = true ∧
    work1653.jac.invOK = true ∧ acceptsUnitSq work1653.out = true := by decide +kernel

def cell1653 : CellCertificate where
  tauBall := tau1653
  contactCenter := center1653
  contactBall := contact1653
  work := work1653
  center_sq := center_sq1653
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1653.1
  jac_ok := checks1653.2.1
  accepted := checks1653.2.2

def tau1654 : RatBall :=
  ⟨⟨7/64, -109/320⟩, 3/640⟩
def center1654 : GaussianRat :=
  ⟨17115273/200000000, -242620769/1000000000⟩
def contact1654 : RatBall := localContactBall tau1654 center1654
def work1654 : RoundedTauEval :=
  evalTau precision tau1654 contact1654 logTwoBall

theorem center_sq1654 : (center1654.re : ℝ)^2 +
    (center1654.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1654]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1654 : work1654.theta.ok = true ∧
    work1654.jac.invOK = true ∧ acceptsUnitSq work1654.out = true := by decide +kernel

def cell1654 : CellCertificate where
  tauBall := tau1654
  contactCenter := center1654
  contactBall := contact1654
  work := work1654
  center_sq := center_sq1654
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1654.1
  jac_ok := checks1654.2.1
  accepted := checks1654.2.2

def tau1655 : RatBall :=
  ⟨⟨37/320, -111/320⟩, 3/640⟩
def center1655 : GaussianRat :=
  ⟨45418507/500000000, -247012717/1000000000⟩
def contact1655 : RatBall := localContactBall tau1655 center1655
def work1655 : RoundedTauEval :=
  evalTau precision tau1655 contact1655 logTwoBall

theorem center_sq1655 : (center1655.re : ℝ)^2 +
    (center1655.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1655]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1655 : work1655.theta.ok = true ∧
    work1655.jac.invOK = true ∧ acceptsUnitSq work1655.out = true := by decide +kernel

def cell1655 : CellCertificate where
  tauBall := tau1655
  contactCenter := center1655
  contactBall := contact1655
  work := work1655
  center_sq := center_sq1655
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1655.1
  jac_ok := checks1655.2.1
  accepted := checks1655.2.2

def cells : List CellCertificate := [cell1648, cell1649, cell1650, cell1651, cell1652, cell1653, cell1654, cell1655]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0206

end


