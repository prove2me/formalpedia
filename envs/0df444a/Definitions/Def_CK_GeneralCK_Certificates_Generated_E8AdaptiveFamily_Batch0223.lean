-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0223
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0223
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:01:02.679046+00:00
-- url     : https://prove2.me/theorems/1c0ec6b2-4ac2-4e27-9c01-6d7142ac86e0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0223` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0223` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0223` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0223 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0223.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0223 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0223

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1784 : RatBall :=
  ⟨⟨67/320, -93/320⟩, 3/640⟩
def center1784 : GaussianRat :=
  ⟨3112069/20000000, -197272757/1000000000⟩
def contact1784 : RatBall := localContactBall tau1784 center1784
def work1784 : RoundedTauEval :=
  evalTau precision tau1784 contact1784 logTwoBall

theorem center_sq1784 : (center1784.re : ℝ)^2 +
    (center1784.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1784]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1784 : work1784.theta.ok = true ∧
    work1784.jac.invOK = true ∧ acceptsUnitSq work1784.out = true := by decide +kernel

def cell1784 : CellCertificate where
  tauBall := tau1784
  contactCenter := center1784
  contactBall := contact1784
  work := work1784
  center_sq := center_sq1784
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1784.1
  jac_ok := checks1784.2.1
  accepted := checks1784.2.2

def tau1785 : RatBall :=
  ⟨⟨69/320, -19/64⟩, 3/640⟩
def center1785 : GaussianRat :=
  ⟨80325427/500000000, -201116047/1000000000⟩
def contact1785 : RatBall := localContactBall tau1785 center1785
def work1785 : RoundedTauEval :=
  evalTau precision tau1785 contact1785 logTwoBall

theorem center_sq1785 : (center1785.re : ℝ)^2 +
    (center1785.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1785]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1785 : work1785.theta.ok = true ∧
    work1785.jac.invOK = true ∧ acceptsUnitSq work1785.out = true := by decide +kernel

def cell1785 : CellCertificate where
  tauBall := tau1785
  contactCenter := center1785
  contactBall := contact1785
  work := work1785
  center_sq := center_sq1785
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1785.1
  jac_ok := checks1785.2.1
  accepted := checks1785.2.2

def tau1786 : RatBall :=
  ⟨⟨71/320, -19/64⟩, 3/640⟩
def center1786 : GaussianRat :=
  ⟨165085801/1000000000, -40098349/200000000⟩
def contact1786 : RatBall := localContactBall tau1786 center1786
def work1786 : RoundedTauEval :=
  evalTau precision tau1786 contact1786 logTwoBall

theorem center_sq1786 : (center1786.re : ℝ)^2 +
    (center1786.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1786]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1786 : work1786.theta.ok = true ∧
    work1786.jac.invOK = true ∧ acceptsUnitSq work1786.out = true := by decide +kernel

def cell1786 : CellCertificate where
  tauBall := tau1786
  contactCenter := center1786
  contactBall := contact1786
  work := work1786
  center_sq := center_sq1786
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1786.1
  jac_ok := checks1786.2.1
  accepted := checks1786.2.2

def tau1787 : RatBall :=
  ⟨⟨69/320, -93/320⟩, 3/640⟩
def center1787 : GaussianRat :=
  ⟨32008397/200000000, -245849/1250000⟩
def contact1787 : RatBall := localContactBall tau1787 center1787
def work1787 : RoundedTauEval :=
  evalTau precision tau1787 contact1787 logTwoBall

theorem center_sq1787 : (center1787.re : ℝ)^2 +
    (center1787.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1787]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1787 : work1787.theta.ok = true ∧
    work1787.jac.invOK = true ∧ acceptsUnitSq work1787.out = true := by decide +kernel

def cell1787 : CellCertificate where
  tauBall := tau1787
  contactCenter := center1787
  contactBall := contact1787
  work := work1787
  center_sq := center_sq1787
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1787.1
  jac_ok := checks1787.2.1
  accepted := checks1787.2.2

def tau1788 : RatBall :=
  ⟨⟨71/320, -93/320⟩, 3/640⟩
def center1788 : GaussianRat :=
  ⟨82231753/500000000, -98036117/500000000⟩
def contact1788 : RatBall := localContactBall tau1788 center1788
def work1788 : RoundedTauEval :=
  evalTau precision tau1788 contact1788 logTwoBall

theorem center_sq1788 : (center1788.re : ℝ)^2 +
    (center1788.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1788]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1788 : work1788.theta.ok = true ∧
    work1788.jac.invOK = true ∧ acceptsUnitSq work1788.out = true := by decide +kernel

def cell1788 : CellCertificate where
  tauBall := tau1788
  contactCenter := center1788
  contactBall := contact1788
  work := work1788
  center_sq := center_sq1788
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1788.1
  jac_ok := checks1788.2.1
  accepted := checks1788.2.2

def tau1789 : RatBall :=
  ⟨⟨73/320, -19/64⟩, 3/640⟩
def center1789 : GaussianRat :=
  ⟨16950309/100000000, -199854009/1000000000⟩
def contact1789 : RatBall := localContactBall tau1789 center1789
def work1789 : RoundedTauEval :=
  evalTau precision tau1789 contact1789 logTwoBall

theorem center_sq1789 : (center1789.re : ℝ)^2 +
    (center1789.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1789]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1789 : work1789.theta.ok = true ∧
    work1789.jac.invOK = true ∧ acceptsUnitSq work1789.out = true := by decide +kernel

def cell1789 : CellCertificate where
  tauBall := tau1789
  contactCenter := center1789
  contactBall := contact1789
  work := work1789
  center_sq := center_sq1789
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1789.1
  jac_ok := checks1789.2.1
  accepted := checks1789.2.2

def tau1790 : RatBall :=
  ⟨⟨15/64, -19/64⟩, 3/640⟩
def center1790 : GaussianRat :=
  ⟨43475599/250000000, -199203157/1000000000⟩
def contact1790 : RatBall := localContactBall tau1790 center1790
def work1790 : RoundedTauEval :=
  evalTau precision tau1790 contact1790 logTwoBall

theorem center_sq1790 : (center1790.re : ℝ)^2 +
    (center1790.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1790]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1790 : work1790.theta.ok = true ∧
    work1790.jac.invOK = true ∧ acceptsUnitSq work1790.out = true := by decide +kernel

def cell1790 : CellCertificate where
  tauBall := tau1790
  contactCenter := center1790
  contactBall := contact1790
  work := work1790
  center_sq := center_sq1790
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1790.1
  jac_ok := checks1790.2.1
  accepted := checks1790.2.2

def tau1791 : RatBall :=
  ⟨⟨73/320, -93/320⟩, 3/640⟩
def center1791 : GaussianRat :=
  ⟨84433841/500000000, -195452163/1000000000⟩
def contact1791 : RatBall := localContactBall tau1791 center1791
def work1791 : RoundedTauEval :=
  evalTau precision tau1791 contact1791 logTwoBall

theorem center_sq1791 : (center1791.re : ℝ)^2 +
    (center1791.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1791]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1791 : work1791.theta.ok = true ∧
    work1791.jac.invOK = true ∧ acceptsUnitSq work1791.out = true := by decide +kernel

def cell1791 : CellCertificate where
  tauBall := tau1791
  contactCenter := center1791
  contactBall := contact1791
  work := work1791
  center_sq := center_sq1791
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1791.1
  jac_ok := checks1791.2.1
  accepted := checks1791.2.2

def cells : List CellCertificate := [cell1784, cell1785, cell1786, cell1787, cell1788, cell1789, cell1790, cell1791]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0223

end


