-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0221
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0221
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:50:53.384935+00:00
-- url     : https://prove2.me/theorems/30cc400b-8ee7-4b04-a205-85ad0eaf2934
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0221` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0221` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0221` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0221 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0221.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0221 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0221

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1768 : RatBall :=
  ⟨⟨73/320, -99/320⟩, 3/640⟩
def center1768 : GaussianRat :=
  ⟨42707047/250000000, -20869737/100000000⟩
def contact1768 : RatBall := localContactBall tau1768 center1768
def work1768 : RoundedTauEval :=
  evalTau precision tau1768 contact1768 logTwoBall

theorem center_sq1768 : (center1768.re : ℝ)^2 +
    (center1768.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1768]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1768 : work1768.theta.ok = true ∧
    work1768.jac.invOK = true ∧ acceptsUnitSq work1768.out = true := by decide +kernel

def cell1768 : CellCertificate where
  tauBall := tau1768
  contactCenter := center1768
  contactBall := contact1768
  work := work1768
  center_sq := center_sq1768
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1768.1
  jac_ok := checks1768.2.1
  accepted := checks1768.2.2

def tau1769 : RatBall :=
  ⟨⟨15/64, -99/320⟩, 3/640⟩
def center1769 : GaussianRat :=
  ⟨35050807/200000000, -8320383/40000000⟩
def contact1769 : RatBall := localContactBall tau1769 center1769
def work1769 : RoundedTauEval :=
  evalTau precision tau1769 contact1769 logTwoBall

theorem center_sq1769 : (center1769.re : ℝ)^2 +
    (center1769.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1769]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1769 : work1769.theta.ok = true ∧
    work1769.jac.invOK = true ∧ acceptsUnitSq work1769.out = true := by decide +kernel

def cell1769 : CellCertificate where
  tauBall := tau1769
  contactCenter := center1769
  contactBall := contact1769
  work := work1769
  center_sq := center_sq1769
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1769.1
  jac_ok := checks1769.2.1
  accepted := checks1769.2.2

def tau1770 : RatBall :=
  ⟨⟨73/320, -97/320⟩, 3/640⟩
def center1770 : GaussianRat :=
  ⟨42539121/250000000, -204268971/1000000000⟩
def contact1770 : RatBall := localContactBall tau1770 center1770
def work1770 : RoundedTauEval :=
  evalTau precision tau1770 contact1770 logTwoBall

theorem center_sq1770 : (center1770.re : ℝ)^2 +
    (center1770.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1770]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1770 : work1770.theta.ok = true ∧
    work1770.jac.invOK = true ∧ acceptsUnitSq work1770.out = true := by decide +kernel

def cell1770 : CellCertificate where
  tauBall := tau1770
  contactCenter := center1770
  contactBall := contact1770
  work := work1770
  center_sq := center_sq1770
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1770.1
  jac_ok := checks1770.2.1
  accepted := checks1770.2.2

def tau1771 : RatBall :=
  ⟨⟨15/64, -97/320⟩, 3/640⟩
def center1771 : GaussianRat :=
  ⟨87284451/500000000, -101799907/500000000⟩
def contact1771 : RatBall := localContactBall tau1771 center1771
def work1771 : RoundedTauEval :=
  evalTau precision tau1771 contact1771 logTwoBall

theorem center_sq1771 : (center1771.re : ℝ)^2 +
    (center1771.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1771]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1771 : work1771.theta.ok = true ∧
    work1771.jac.invOK = true ∧ acceptsUnitSq work1771.out = true := by decide +kernel

def cell1771 : CellCertificate where
  tauBall := tau1771
  contactCenter := center1771
  contactBall := contact1771
  work := work1771
  center_sq := center_sq1771
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1771.1
  jac_ok := checks1771.2.1
  accepted := checks1771.2.2

def tau1772 : RatBall :=
  ⟨⟨77/320, -99/320⟩, 3/640⟩
def center1772 : GaussianRat :=
  ⟨179660917/1000000000, -207308367/1000000000⟩
def contact1772 : RatBall := localContactBall tau1772 center1772
def work1772 : RoundedTauEval :=
  evalTau precision tau1772 contact1772 logTwoBall

theorem center_sq1772 : (center1772.re : ℝ)^2 +
    (center1772.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1772]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1772 : work1772.theta.ok = true ∧
    work1772.jac.invOK = true ∧ acceptsUnitSq work1772.out = true := by decide +kernel

def cell1772 : CellCertificate where
  tauBall := tau1772
  contactCenter := center1772
  contactBall := contact1772
  work := work1772
  center_sq := center_sq1772
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1772.1
  jac_ok := checks1772.2.1
  accepted := checks1772.2.2

def tau1773 : RatBall :=
  ⟨⟨79/320, -99/320⟩, 3/640⟩
def center1773 : GaussianRat :=
  ⟨184048527/1000000000, -206594091/1000000000⟩
def contact1773 : RatBall := localContactBall tau1773 center1773
def work1773 : RoundedTauEval :=
  evalTau precision tau1773 contact1773 logTwoBall

theorem center_sq1773 : (center1773.re : ℝ)^2 +
    (center1773.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1773]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1773 : work1773.theta.ok = true ∧
    work1773.jac.invOK = true ∧ acceptsUnitSq work1773.out = true := by decide +kernel

def cell1773 : CellCertificate where
  tauBall := tau1773
  contactCenter := center1773
  contactBall := contact1773
  work := work1773
  center_sq := center_sq1773
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1773.1
  jac_ok := checks1773.2.1
  accepted := checks1773.2.2

def tau1774 : RatBall :=
  ⟨⟨77/320, -97/320⟩, 3/640⟩
def center1774 : GaussianRat :=
  ⟨35792539/200000000, -40583511/200000000⟩
def contact1774 : RatBall := localContactBall tau1774 center1774
def work1774 : RoundedTauEval :=
  evalTau precision tau1774 contact1774 logTwoBall

theorem center_sq1774 : (center1774.re : ℝ)^2 +
    (center1774.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1774]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1774 : work1774.theta.ok = true ∧
    work1774.jac.invOK = true ∧ acceptsUnitSq work1774.out = true := by decide +kernel

def cell1774 : CellCertificate where
  tauBall := tau1774
  contactCenter := center1774
  contactBall := contact1774
  work := work1774
  center_sq := center_sq1774
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1774.1
  jac_ok := checks1774.2.1
  accepted := checks1774.2.2

def tau1775 : RatBall :=
  ⟨⟨79/320, -97/320⟩, 3/640⟩
def center1775 : GaussianRat :=
  ⟨183337559/1000000000, -202222527/1000000000⟩
def contact1775 : RatBall := localContactBall tau1775 center1775
def work1775 : RoundedTauEval :=
  evalTau precision tau1775 contact1775 logTwoBall

theorem center_sq1775 : (center1775.re : ℝ)^2 +
    (center1775.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1775]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1775 : work1775.theta.ok = true ∧
    work1775.jac.invOK = true ∧ acceptsUnitSq work1775.out = true := by decide +kernel

def cell1775 : CellCertificate where
  tauBall := tau1775
  contactCenter := center1775
  contactBall := contact1775
  work := work1775
  center_sq := center_sq1775
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1775.1
  jac_ok := checks1775.2.1
  accepted := checks1775.2.2

def cells : List CellCertificate := [cell1768, cell1769, cell1770, cell1771, cell1772, cell1773, cell1774, cell1775]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0221

end


