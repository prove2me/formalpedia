-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0219
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0219
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:33:41.228867+00:00
-- url     : https://prove2.me/theorems/0370bed2-9a60-4b61-b3fe-19d4e471a620
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0219` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0219` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0219` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0219 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0219.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0219 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0219

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1752 : RatBall :=
  ⟨⟨71/320, -101/320⟩, 3/640⟩
def center1752 : GaussianRat :=
  ⟨167059951/1000000000, -10691611/50000000⟩
def contact1752 : RatBall := localContactBall tau1752 center1752
def work1752 : RoundedTauEval :=
  evalTau precision tau1752 contact1752 logTwoBall

theorem center_sq1752 : (center1752.re : ℝ)^2 +
    (center1752.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1752]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1752 : work1752.theta.ok = true ∧
    work1752.jac.invOK = true ∧ acceptsUnitSq work1752.out = true := by decide +kernel

def cell1752 : CellCertificate where
  tauBall := tau1752
  contactCenter := center1752
  contactBall := contact1752
  work := work1752
  center_sq := center_sq1752
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1752.1
  jac_ok := checks1752.2.1
  accepted := checks1752.2.2

def tau1753 : RatBall :=
  ⟨⟨13/64, -99/320⟩, 3/640⟩
def center1753 : GaussianRat :=
  ⟨30588339/200000000, -211307539/1000000000⟩
def contact1753 : RatBall := localContactBall tau1753 center1753
def work1753 : RoundedTauEval :=
  evalTau precision tau1753 contact1753 logTwoBall

theorem center_sq1753 : (center1753.re : ℝ)^2 +
    (center1753.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1753]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1753 : work1753.theta.ok = true ∧
    work1753.jac.invOK = true ∧ acceptsUnitSq work1753.out = true := by decide +kernel

def cell1753 : CellCertificate where
  tauBall := tau1753
  contactCenter := center1753
  contactBall := contact1753
  work := work1753
  center_sq := center_sq1753
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1753.1
  jac_ok := checks1753.2.1
  accepted := checks1753.2.2

def tau1754 : RatBall :=
  ⟨⟨67/320, -99/320⟩, 3/640⟩
def center1754 : GaussianRat :=
  ⟨157440099/1000000000, -210676827/1000000000⟩
def contact1754 : RatBall := localContactBall tau1754 center1754
def work1754 : RoundedTauEval :=
  evalTau precision tau1754 contact1754 logTwoBall

theorem center_sq1754 : (center1754.re : ℝ)^2 +
    (center1754.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1754]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1754 : work1754.theta.ok = true ∧
    work1754.jac.invOK = true ∧ acceptsUnitSq work1754.out = true := by decide +kernel

def cell1754 : CellCertificate where
  tauBall := tau1754
  contactCenter := center1754
  contactBall := contact1754
  work := work1754
  center_sq := center_sq1754
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1754.1
  jac_ok := checks1754.2.1
  accepted := checks1754.2.2

def tau1755 : RatBall :=
  ⟨⟨13/64, -97/320⟩, 3/640⟩
def center1755 : GaussianRat :=
  ⟨9520441/62500000, -206807941/1000000000⟩
def contact1755 : RatBall := localContactBall tau1755 center1755
def work1755 : RoundedTauEval :=
  evalTau precision tau1755 contact1755 logTwoBall

theorem center_sq1755 : (center1755.re : ℝ)^2 +
    (center1755.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1755]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1755 : work1755.theta.ok = true ∧
    work1755.jac.invOK = true ∧ acceptsUnitSq work1755.out = true := by decide +kernel

def cell1755 : CellCertificate where
  tauBall := tau1755
  contactCenter := center1755
  contactBall := contact1755
  work := work1755
  center_sq := center_sq1755
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1755.1
  jac_ok := checks1755.2.1
  accepted := checks1755.2.2

def tau1756 : RatBall :=
  ⟨⟨67/320, -97/320⟩, 3/640⟩
def center1756 : GaussianRat :=
  ⟨19601337/125000000, -103097251/500000000⟩
def contact1756 : RatBall := localContactBall tau1756 center1756
def work1756 : RoundedTauEval :=
  evalTau precision tau1756 contact1756 logTwoBall

theorem center_sq1756 : (center1756.re : ℝ)^2 +
    (center1756.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1756]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1756 : work1756.theta.ok = true ∧
    work1756.jac.invOK = true ∧ acceptsUnitSq work1756.out = true := by decide +kernel

def cell1756 : CellCertificate where
  tauBall := tau1756
  contactCenter := center1756
  contactBall := contact1756
  work := work1756
  center_sq := center_sq1756
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1756.1
  jac_ok := checks1756.2.1
  accepted := checks1756.2.2

def tau1757 : RatBall :=
  ⟨⟨69/320, -99/320⟩, 3/640⟩
def center1757 : GaussianRat :=
  ⟨161920883/1000000000, -210031337/1000000000⟩
def contact1757 : RatBall := localContactBall tau1757 center1757
def work1757 : RoundedTauEval :=
  evalTau precision tau1757 contact1757 logTwoBall

theorem center_sq1757 : (center1757.re : ℝ)^2 +
    (center1757.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1757]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1757 : work1757.theta.ok = true ∧
    work1757.jac.invOK = true ∧ acceptsUnitSq work1757.out = true := by decide +kernel

def cell1757 : CellCertificate where
  tauBall := tau1757
  contactCenter := center1757
  contactBall := contact1757
  work := work1757
  center_sq := center_sq1757
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1757.1
  jac_ok := checks1757.2.1
  accepted := checks1757.2.2

def tau1758 : RatBall :=
  ⟨⟨71/320, -99/320⟩, 3/640⟩
def center1758 : GaussianRat :=
  ⟨83191847/500000000, -52342851/250000000⟩
def contact1758 : RatBall := localContactBall tau1758 center1758
def work1758 : RoundedTauEval :=
  evalTau precision tau1758 contact1758 logTwoBall

theorem center_sq1758 : (center1758.re : ℝ)^2 +
    (center1758.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1758]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1758 : work1758.theta.ok = true ∧
    work1758.jac.invOK = true ∧ acceptsUnitSq work1758.out = true := by decide +kernel

def cell1758 : CellCertificate where
  tauBall := tau1758
  contactCenter := center1758
  contactBall := contact1758
  work := work1758
  center_sq := center_sq1758
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1758.1
  jac_ok := checks1758.2.1
  accepted := checks1758.2.2

def tau1759 : RatBall :=
  ⟨⟨69/320, -97/320⟩, 3/640⟩
def center1759 : GaussianRat :=
  ⟨161277047/1000000000, -51391661/250000000⟩
def contact1759 : RatBall := localContactBall tau1759 center1759
def work1759 : RoundedTauEval :=
  evalTau precision tau1759 contact1759 logTwoBall

theorem center_sq1759 : (center1759.re : ℝ)^2 +
    (center1759.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1759]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1759 : work1759.theta.ok = true ∧
    work1759.jac.invOK = true ∧ acceptsUnitSq work1759.out = true := by decide +kernel

def cell1759 : CellCertificate where
  tauBall := tau1759
  contactCenter := center1759
  contactBall := contact1759
  work := work1759
  center_sq := center_sq1759
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1759.1
  jac_ok := checks1759.2.1
  accepted := checks1759.2.2

def cells : List CellCertificate := [cell1752, cell1753, cell1754, cell1755, cell1756, cell1757, cell1758, cell1759]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0219

end


