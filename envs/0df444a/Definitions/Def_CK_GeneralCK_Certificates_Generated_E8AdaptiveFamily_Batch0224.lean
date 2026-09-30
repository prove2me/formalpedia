-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0224
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0224
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:25:30.436089+00:00
-- url     : https://prove2.me/theorems/2e175e65-f051-4b77-88b1-a182c7ab6426
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0224` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0224` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0224` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0224 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0224.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0224 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0224

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1792 : RatBall :=
  ⟨⟨15/64, -93/320⟩, 3/640⟩
def center1792 : GaussianRat :=
  ⟨173254189/1000000000, -38963859/200000000⟩
def contact1792 : RatBall := localContactBall tau1792 center1792
def work1792 : RoundedTauEval :=
  evalTau precision tau1792 contact1792 logTwoBall

theorem center_sq1792 : (center1792.re : ℝ)^2 +
    (center1792.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1792]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1792 : work1792.theta.ok = true ∧
    work1792.jac.invOK = true ∧ acceptsUnitSq work1792.out = true := by decide +kernel

def cell1792 : CellCertificate where
  tauBall := tau1792
  contactCenter := center1792
  contactBall := contact1792
  work := work1792
  center_sq := center_sq1792
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1792.1
  jac_ok := checks1792.2.1
  accepted := checks1792.2.2

def tau1793 : RatBall :=
  ⟨⟨77/320, -19/64⟩, 3/640⟩
def center1793 : GaussianRat :=
  ⟨35656681/200000000, -198539511/1000000000⟩
def contact1793 : RatBall := localContactBall tau1793 center1793
def work1793 : RoundedTauEval :=
  evalTau precision tau1793 contact1793 logTwoBall

theorem center_sq1793 : (center1793.re : ℝ)^2 +
    (center1793.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1793]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1793 : work1793.theta.ok = true ∧
    work1793.jac.invOK = true ∧ acceptsUnitSq work1793.out = true := by decide +kernel

def cell1793 : CellCertificate where
  tauBall := tau1793
  contactCenter := center1793
  contactBall := contact1793
  work := work1793
  center_sq := center_sq1793
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1793.1
  jac_ok := checks1793.2.1
  accepted := checks1793.2.2

def tau1794 : RatBall :=
  ⟨⟨79/320, -19/64⟩, 3/640⟩
def center1794 : GaussianRat :=
  ⟨91322907/500000000, -98931697/500000000⟩
def contact1794 : RatBall := localContactBall tau1794 center1794
def work1794 : RoundedTauEval :=
  evalTau precision tau1794 contact1794 logTwoBall

theorem center_sq1794 : (center1794.re : ℝ)^2 +
    (center1794.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1794]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1794 : work1794.theta.ok = true ∧
    work1794.jac.invOK = true ∧ acceptsUnitSq work1794.out = true := by decide +kernel

def cell1794 : CellCertificate where
  tauBall := tau1794
  contactCenter := center1794
  contactBall := contact1794
  work := work1794
  center_sq := center_sq1794
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1794.1
  jac_ok := checks1794.2.1
  accepted := checks1794.2.2

def tau1795 : RatBall :=
  ⟨⟨77/320, -93/320⟩, 3/640⟩
def center1795 : GaussianRat :=
  ⟨44405679/250000000, -194173939/1000000000⟩
def contact1795 : RatBall := localContactBall tau1795 center1795
def work1795 : RoundedTauEval :=
  evalTau precision tau1795 contact1795 logTwoBall

theorem center_sq1795 : (center1795.re : ℝ)^2 +
    (center1795.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1795]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1795 : work1795.theta.ok = true ∧
    work1795.jac.invOK = true ∧ acceptsUnitSq work1795.out = true := by decide +kernel

def cell1795 : CellCertificate where
  tauBall := tau1795
  contactCenter := center1795
  contactBall := contact1795
  work := work1795
  center_sq := center_sq1795
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1795.1
  jac_ok := checks1795.2.1
  accepted := checks1795.2.2

def tau1796 : RatBall :=
  ⟨⟨79/320, -93/320⟩, 3/640⟩
def center1796 : GaussianRat :=
  ⟨90986481/500000000, -24189551/125000000⟩
def contact1796 : RatBall := localContactBall tau1796 center1796
def work1796 : RoundedTauEval :=
  evalTau precision tau1796 contact1796 logTwoBall

theorem center_sq1796 : (center1796.re : ℝ)^2 +
    (center1796.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1796]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1796 : work1796.theta.ok = true ∧
    work1796.jac.invOK = true ∧ acceptsUnitSq work1796.out = true := by decide +kernel

def cell1796 : CellCertificate where
  tauBall := tau1796
  contactCenter := center1796
  contactBall := contact1796
  work := work1796
  center_sq := center_sq1796
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1796.1
  jac_ok := checks1796.2.1
  accepted := checks1796.2.2

def tau1797 : RatBall :=
  ⟨⟨73/320, -91/320⟩, 3/640⟩
def center1797 : GaussianRat :=
  ⟨33649989/200000000, -38212623/200000000⟩
def contact1797 : RatBall := localContactBall tau1797 center1797
def work1797 : RoundedTauEval :=
  evalTau precision tau1797 contact1797 logTwoBall

theorem center_sq1797 : (center1797.re : ℝ)^2 +
    (center1797.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1797]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1797 : work1797.theta.ok = true ∧
    work1797.jac.invOK = true ∧ acceptsUnitSq work1797.out = true := by decide +kernel

def cell1797 : CellCertificate where
  tauBall := tau1797
  contactCenter := center1797
  contactBall := contact1797
  work := work1797
  center_sq := center_sq1797
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1797.1
  jac_ok := checks1797.2.1
  accepted := checks1797.2.2

def tau1798 : RatBall :=
  ⟨⟨15/64, -91/320⟩, 3/640⟩
def center1798 : GaussianRat :=
  ⟨34524793/200000000, -2380599/12500000⟩
def contact1798 : RatBall := localContactBall tau1798 center1798
def work1798 : RoundedTauEval :=
  evalTau precision tau1798 contact1798 logTwoBall

theorem center_sq1798 : (center1798.re : ℝ)^2 +
    (center1798.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1798]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1798 : work1798.theta.ok = true ∧
    work1798.jac.invOK = true ∧ acceptsUnitSq work1798.out = true := by decide +kernel

def cell1798 : CellCertificate where
  tauBall := tau1798
  contactCenter := center1798
  contactBall := contact1798
  work := work1798
  center_sq := center_sq1798
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1798.1
  jac_ok := checks1798.2.1
  accepted := checks1798.2.2

def tau1799 : RatBall :=
  ⟨⟨73/320, -89/320⟩, 3/640⟩
def center1799 : GaussianRat :=
  ⟨6705983/40000000, -46671637/250000000⟩
def contact1799 : RatBall := localContactBall tau1799 center1799
def work1799 : RoundedTauEval :=
  evalTau precision tau1799 contact1799 logTwoBall

theorem center_sq1799 : (center1799.re : ℝ)^2 +
    (center1799.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1799]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1799 : work1799.theta.ok = true ∧
    work1799.jac.invOK = true ∧ acceptsUnitSq work1799.out = true := by decide +kernel

def cell1799 : CellCertificate where
  tauBall := tau1799
  contactCenter := center1799
  contactBall := contact1799
  work := work1799
  center_sq := center_sq1799
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1799.1
  jac_ok := checks1799.2.1
  accepted := checks1799.2.2

def cells : List CellCertificate := [cell1792, cell1793, cell1794, cell1795, cell1796, cell1797, cell1798, cell1799]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0224

end


