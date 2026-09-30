-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0211
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0211
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:52:04.316764+00:00
-- url     : https://prove2.me/theorems/8830f72b-2e4b-441e-813e-4deb355c6d8f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0211` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0211` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0211` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0211 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0211.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0211 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0211

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1688 : RatBall :=
  ⟨⟨11/64, -111/320⟩, 3/640⟩
def center1688 : GaussianRat :=
  ⟨133746201/1000000000, -121037589/500000000⟩
def contact1688 : RatBall := localContactBall tau1688 center1688
def work1688 : RoundedTauEval :=
  evalTau precision tau1688 contact1688 logTwoBall

theorem center_sq1688 : (center1688.re : ℝ)^2 +
    (center1688.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1688]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1688 : work1688.theta.ok = true ∧
    work1688.jac.invOK = true ∧ acceptsUnitSq work1688.out = true := by decide +kernel

def cell1688 : CellCertificate where
  tauBall := tau1688
  contactCenter := center1688
  contactBall := contact1688
  work := work1688
  center_sq := center_sq1688
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1688.1
  jac_ok := checks1688.2.1
  accepted := checks1688.2.2

def tau1689 : RatBall :=
  ⟨⟨53/320, -109/320⟩, 3/640⟩
def center1689 : GaussianRat :=
  ⟨25685587/200000000, -238002417/1000000000⟩
def contact1689 : RatBall := localContactBall tau1689 center1689
def work1689 : RoundedTauEval :=
  evalTau precision tau1689 contact1689 logTwoBall

theorem center_sq1689 : (center1689.re : ℝ)^2 +
    (center1689.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1689]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1689 : work1689.theta.ok = true ∧
    work1689.jac.invOK = true ∧ acceptsUnitSq work1689.out = true := by decide +kernel

def cell1689 : CellCertificate where
  tauBall := tau1689
  contactCenter := center1689
  contactBall := contact1689
  work := work1689
  center_sq := center_sq1689
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1689.1
  jac_ok := checks1689.2.1
  accepted := checks1689.2.2

def tau1690 : RatBall :=
  ⟨⟨11/64, -109/320⟩, 3/640⟩
def center1690 : GaussianRat :=
  ⟨133113831/1000000000, -118694053/500000000⟩
def contact1690 : RatBall := localContactBall tau1690 center1690
def work1690 : RoundedTauEval :=
  evalTau precision tau1690 contact1690 logTwoBall

theorem center_sq1690 : (center1690.re : ℝ)^2 +
    (center1690.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1690]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1690 : work1690.theta.ok = true ∧
    work1690.jac.invOK = true ∧ acceptsUnitSq work1690.out = true := by decide +kernel

def cell1690 : CellCertificate where
  tauBall := tau1690
  contactCenter := center1690
  contactBall := contact1690
  work := work1690
  center_sq := center_sq1690
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1690.1
  jac_ok := checks1690.2.1
  accepted := checks1690.2.2

def tau1691 : RatBall :=
  ⟨⟨49/320, -107/320⟩, 3/640⟩
def center1691 : GaussianRat :=
  ⟨5922481/50000000, -234456553/1000000000⟩
def contact1691 : RatBall := localContactBall tau1691 center1691
def work1691 : RoundedTauEval :=
  evalTau precision tau1691 contact1691 logTwoBall

theorem center_sq1691 : (center1691.re : ℝ)^2 +
    (center1691.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1691]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1691 : work1691.theta.ok = true ∧
    work1691.jac.invOK = true ∧ acceptsUnitSq work1691.out = true := by decide +kernel

def cell1691 : CellCertificate where
  tauBall := tau1691
  contactCenter := center1691
  contactBall := contact1691
  work := work1691
  center_sq := center_sq1691
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1691.1
  jac_ok := checks1691.2.1
  accepted := checks1691.2.2

def tau1692 : RatBall :=
  ⟨⟨51/320, -107/320⟩, 3/640⟩
def center1692 : GaussianRat :=
  ⟨24629661/200000000, -233896771/1000000000⟩
def contact1692 : RatBall := localContactBall tau1692 center1692
def work1692 : RoundedTauEval :=
  evalTau precision tau1692 contact1692 logTwoBall

theorem center_sq1692 : (center1692.re : ℝ)^2 +
    (center1692.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1692]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1692 : work1692.theta.ok = true ∧
    work1692.jac.invOK = true ∧ acceptsUnitSq work1692.out = true := by decide +kernel

def cell1692 : CellCertificate where
  tauBall := tau1692
  contactCenter := center1692
  contactBall := contact1692
  work := work1692
  center_sq := center_sq1692
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1692.1
  jac_ok := checks1692.2.1
  accepted := checks1692.2.2

def tau1693 : RatBall :=
  ⟨⟨49/320, -21/64⟩, 3/640⟩
def center1693 : GaussianRat :=
  ⟨58953523/500000000, -57439977/250000000⟩
def contact1693 : RatBall := localContactBall tau1693 center1693
def work1693 : RoundedTauEval :=
  evalTau precision tau1693 contact1693 logTwoBall

theorem center_sq1693 : (center1693.re : ℝ)^2 +
    (center1693.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1693]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1693 : work1693.theta.ok = true ∧
    work1693.jac.invOK = true ∧ acceptsUnitSq work1693.out = true := by decide +kernel

def cell1693 : CellCertificate where
  tauBall := tau1693
  contactCenter := center1693
  contactBall := contact1693
  work := work1693
  center_sq := center_sq1693
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1693.1
  jac_ok := checks1693.2.1
  accepted := checks1693.2.2

def tau1694 : RatBall :=
  ⟨⟨51/320, -21/64⟩, 3/640⟩
def center1694 : GaussianRat :=
  ⟨122586619/1000000000, -229215321/1000000000⟩
def contact1694 : RatBall := localContactBall tau1694 center1694
def work1694 : RoundedTauEval :=
  evalTau precision tau1694 contact1694 logTwoBall

theorem center_sq1694 : (center1694.re : ℝ)^2 +
    (center1694.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1694]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1694 : work1694.theta.ok = true ∧
    work1694.jac.invOK = true ∧ acceptsUnitSq work1694.out = true := by decide +kernel

def cell1694 : CellCertificate where
  tauBall := tau1694
  contactCenter := center1694
  contactBall := contact1694
  work := work1694
  center_sq := center_sq1694
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1694.1
  jac_ok := checks1694.2.1
  accepted := checks1694.2.2

def tau1695 : RatBall :=
  ⟨⟨53/320, -107/320⟩, 3/640⟩
def center1695 : GaussianRat :=
  ⟨15978923/125000000, -233317801/1000000000⟩
def contact1695 : RatBall := localContactBall tau1695 center1695
def work1695 : RoundedTauEval :=
  evalTau precision tau1695 contact1695 logTwoBall

theorem center_sq1695 : (center1695.re : ℝ)^2 +
    (center1695.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1695]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1695 : work1695.theta.ok = true ∧
    work1695.jac.invOK = true ∧ acceptsUnitSq work1695.out = true := by decide +kernel

def cell1695 : CellCertificate where
  tauBall := tau1695
  contactCenter := center1695
  contactBall := contact1695
  work := work1695
  center_sq := center_sq1695
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1695.1
  jac_ok := checks1695.2.1
  accepted := checks1695.2.2

def cells : List CellCertificate := [cell1688, cell1689, cell1690, cell1691, cell1692, cell1693, cell1694, cell1695]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0211

end


