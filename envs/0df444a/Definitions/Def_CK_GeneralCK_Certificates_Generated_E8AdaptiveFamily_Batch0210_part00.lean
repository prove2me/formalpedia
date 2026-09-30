-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0210_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0210_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:04:04.426751+00:00
-- url     : https://prove2.me/theorems/650bce2f-f83f-49b9-8b58-040cb99f23e8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0210 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1680 : RatBall :=
  ⟨⟨47/320, -103/320⟩, 3/640⟩
def center1680 : GaussianRat :=
  ⟨704399/6250000, -112796733/500000000⟩
def contact1680 : RatBall := localContactBall tau1680 center1680
def work1680 : RoundedTauEval :=
  evalTau precision tau1680 contact1680 logTwoBall

theorem center_sq1680 : (center1680.re : ℝ)^2 +
    (center1680.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1680]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1680 : work1680.theta.ok = true ∧
    work1680.jac.invOK = true ∧ acceptsUnitSq work1680.out = true := by decide +kernel

def cell1680 : CellCertificate where
  tauBall := tau1680
  contactCenter := center1680
  contactBall := contact1680
  work := work1680
  center_sq := center_sq1680
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1680.1
  jac_ok := checks1680.2.1
  accepted := checks1680.2.2

def tau1681 : RatBall :=
  ⟨⟨9/64, -101/320⟩, 3/640⟩
def center1681 : GaussianRat :=
  ⟨53769161/500000000, -221399049/1000000000⟩
def contact1681 : RatBall := localContactBall tau1681 center1681
def work1681 : RoundedTauEval :=
  evalTau precision tau1681 contact1681 logTwoBall

theorem center_sq1681 : (center1681.re : ℝ)^2 +
    (center1681.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1681]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1681 : work1681.theta.ok = true ∧
    work1681.jac.invOK = true ∧ acceptsUnitSq work1681.out = true := by decide +kernel

def cell1681 : CellCertificate where
  tauBall := tau1681
  contactCenter := center1681
  contactBall := contact1681
  work := work1681
  center_sq := center_sq1681
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1681.1
  jac_ok := checks1681.2.1
  accepted := checks1681.2.2

def tau1682 : RatBall :=
  ⟨⟨47/320, -101/320⟩, 3/640⟩
def center1682 : GaussianRat :=
  ⟨112208983/1000000000, -220920311/1000000000⟩
def contact1682 : RatBall := localContactBall tau1682 center1682
def work1682 : RoundedTauEval :=
  evalTau precision tau1682 contact1682 logTwoBall

theorem center_sq1682 : (center1682.re : ℝ)^2 +
    (center1682.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1682]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1682 : work1682.theta.ok = true ∧
    work1682.jac.invOK = true ∧ acceptsUnitSq work1682.out = true := by decide +kernel

def cell1682 : CellCertificate where
  tauBall := tau1682
  contactCenter := center1682
  contactBall := contact1682
  work := work1682
  center_sq := center_sq1682
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1682.1
  jac_ok := checks1682.2.1
  accepted := checks1682.2.2

def tau1683 : RatBall :=
  ⟨⟨49/320, -111/320⟩, 3/640⟩
def center1683 : GaussianRat :=
  ⟨29895113/250000000, -121954461/500000000⟩
def contact1683 : RatBall := localContactBall tau1683 center1683
def work1683 : RoundedTauEval :=
  evalTau precision tau1683 contact1683 logTwoBall

theorem center_sq1683 : (center1683.re : ℝ)^2 +
    (center1683.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1683]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1683 : work1683.theta.ok = true ∧
    work1683.jac.invOK = true ∧ acceptsUnitSq work1683.out = true := by decide +kernel

def cell1683 : CellCertificate where
  tauBall := tau1683
  contactCenter := center1683
  contactBall := contact1683
  work := work1683
  center_sq := center_sq1683
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1683.1
  jac_ok := checks1683.2.1
  accepted := checks1683.2.2

def tau1684 : RatBall :=
  ⟨⟨51/320, -111/320⟩, 3/640⟩
def center1684 : GaussianRat :=
  ⟨124318847/1000000000, -121658863/500000000⟩
def contact1684 : RatBall := localContactBall tau1684 center1684
def work1684 : RoundedTauEval :=
  evalTau precision tau1684 contact1684 logTwoBall

theorem center_sq1684 : (center1684.re : ℝ)^2 +
    (center1684.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1684]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1684 : work1684.theta.ok = true ∧
    work1684.jac.invOK = true ∧ acceptsUnitSq work1684.out = true := by decide +kernel

def cell1684 : CellCertificate where
  tauBall := tau1684
  contactCenter := center1684
  contactBall := contact1684
  work := work1684
  center_sq := center_sq1684
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1684.1
  jac_ok := checks1684.2.1
  accepted := checks1684.2.2

def tau1685 : RatBall :=
  ⟨⟨49/320, -109/320⟩, 3/640⟩
def center1685 : GaussianRat :=
  ⟨119007309/1000000000, -59793181/250000000⟩
def contact1685 : RatBall := localContactBall tau1685 center1685
def work1685 : RoundedTauEval :=
  evalTau precision tau1685 contact1685 logTwoBall

theorem center_sq1685 : (center1685.re : ℝ)^2 +
    (center1685.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1685]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1685 : work1685.theta.ok = true ∧
    work1685.jac.invOK = true ∧ acceptsUnitSq work1685.out = true := by decide +kernel

def cell1685 : CellCertificate where
  tauBall := tau1685
  contactCenter := center1685
  contactBall := contact1685
  work := work1685
  center_sq := center_sq1685
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1685.1
  jac_ok := checks1685.2.1
  accepted := checks1685.2.2

def tau1686 : RatBall :=
  ⟨⟨51/320, -109/320⟩, 3/640⟩
def center1686 : GaussianRat :=
  ⟨61862799/500000000, -238597409/1000000000⟩
def contact1686 : RatBall := localContactBall tau1686 center1686
def work1686 : RoundedTauEval :=
  evalTau precision tau1686 contact1686 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210


