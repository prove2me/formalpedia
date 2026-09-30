-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0216
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0216
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:48:17.809781+00:00
-- url     : https://prove2.me/theorems/859892d7-8445-4284-9869-5bf9e63c4d62
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0216` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0216` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0216` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0216 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0216.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0216 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0216

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1728 : RatBall :=
  ⟨⟨63/320, -101/320⟩, 3/640⟩
def center1728 : GaussianRat :=
  ⟨74521233/500000000, -108227539/500000000⟩
def contact1728 : RatBall := localContactBall tau1728 center1728
def work1728 : RoundedTauEval :=
  evalTau precision tau1728 contact1728 logTwoBall

theorem center_sq1728 : (center1728.re : ℝ)^2 +
    (center1728.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1728]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1728 : work1728.theta.ok = true ∧
    work1728.jac.invOK = true ∧ acceptsUnitSq work1728.out = true := by decide +kernel

def cell1728 : CellCertificate where
  tauBall := tau1728
  contactCenter := center1728
  contactBall := contact1728
  work := work1728
  center_sq := center_sq1728
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1728.1
  jac_ok := checks1728.2.1
  accepted := checks1728.2.2

def tau1729 : RatBall :=
  ⟨⟨57/320, -99/320⟩, 3/640⟩
def center1729 : GaussianRat :=
  ⟨5391177/40000000, -106838001/500000000⟩
def contact1729 : RatBall := localContactBall tau1729 center1729
def work1729 : RoundedTauEval :=
  evalTau precision tau1729 contact1729 logTwoBall

theorem center_sq1729 : (center1729.re : ℝ)^2 +
    (center1729.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1729]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1729 : work1729.theta.ok = true ∧
    work1729.jac.invOK = true ∧ acceptsUnitSq work1729.out = true := by decide +kernel

def cell1729 : CellCertificate where
  tauBall := tau1729
  contactCenter := center1729
  contactBall := contact1729
  work := work1729
  center_sq := center_sq1729
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1729.1
  jac_ok := checks1729.2.1
  accepted := checks1729.2.2

def tau1730 : RatBall :=
  ⟨⟨59/320, -99/320⟩, 3/640⟩
def center1730 : GaussianRat :=
  ⟨34836127/250000000, -53276923/250000000⟩
def contact1730 : RatBall := localContactBall tau1730 center1730
def work1730 : RoundedTauEval :=
  evalTau precision tau1730 contact1730 logTwoBall

theorem center_sq1730 : (center1730.re : ℝ)^2 +
    (center1730.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1730]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1730 : work1730.theta.ok = true ∧
    work1730.jac.invOK = true ∧ acceptsUnitSq work1730.out = true := by decide +kernel

def cell1730 : CellCertificate where
  tauBall := tau1730
  contactCenter := center1730
  contactBall := contact1730
  work := work1730
  center_sq := center_sq1730
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1730.1
  jac_ok := checks1730.2.1
  accepted := checks1730.2.2

def tau1731 : RatBall :=
  ⟨⟨57/320, -97/320⟩, 3/640⟩
def center1731 : GaussianRat :=
  ⟨67113521/500000000, -52277787/250000000⟩
def contact1731 : RatBall := localContactBall tau1731 center1731
def work1731 : RoundedTauEval :=
  evalTau precision tau1731 contact1731 logTwoBall

theorem center_sq1731 : (center1731.re : ℝ)^2 +
    (center1731.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1731]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1731 : work1731.theta.ok = true ∧
    work1731.jac.invOK = true ∧ acceptsUnitSq work1731.out = true := by decide +kernel

def cell1731 : CellCertificate where
  tauBall := tau1731
  contactCenter := center1731
  contactBall := contact1731
  work := work1731
  center_sq := center_sq1731
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1731.1
  jac_ok := checks1731.2.1
  accepted := checks1731.2.2

def tau1732 : RatBall :=
  ⟨⟨59/320, -97/320⟩, 3/640⟩
def center1732 : GaussianRat :=
  ⟨13877609/100000000, -208558553/1000000000⟩
def contact1732 : RatBall := localContactBall tau1732 center1732
def work1732 : RoundedTauEval :=
  evalTau precision tau1732 contact1732 logTwoBall

theorem center_sq1732 : (center1732.re : ℝ)^2 +
    (center1732.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1732]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1732 : work1732.theta.ok = true ∧
    work1732.jac.invOK = true ∧ acceptsUnitSq work1732.out = true := by decide +kernel

def cell1732 : CellCertificate where
  tauBall := tau1732
  contactCenter := center1732
  contactBall := contact1732
  work := work1732
  center_sq := center_sq1732
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1732.1
  jac_ok := checks1732.2.1
  accepted := checks1732.2.2

def tau1733 : RatBall :=
  ⟨⟨61/320, -99/320⟩, 3/640⟩
def center1733 : GaussianRat :=
  ⟨28778703/200000000, -106261649/500000000⟩
def contact1733 : RatBall := localContactBall tau1733 center1733
def work1733 : RoundedTauEval :=
  evalTau precision tau1733 contact1733 logTwoBall

theorem center_sq1733 : (center1733.re : ℝ)^2 +
    (center1733.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1733]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1733 : work1733.theta.ok = true ∧
    work1733.jac.invOK = true ∧ acceptsUnitSq work1733.out = true := by decide +kernel

def cell1733 : CellCertificate where
  tauBall := tau1733
  contactCenter := center1733
  contactBall := contact1733
  work := work1733
  center_sq := center_sq1733
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1733.1
  jac_ok := checks1733.2.1
  accepted := checks1733.2.2

def tau1734 : RatBall :=
  ⟨⟨63/320, -99/320⟩, 3/640⟩
def center1734 : GaussianRat :=
  ⟨148426041/1000000000, -105961569/500000000⟩
def contact1734 : RatBall := localContactBall tau1734 center1734
def work1734 : RoundedTauEval :=
  evalTau precision tau1734 contact1734 logTwoBall

theorem center_sq1734 : (center1734.re : ℝ)^2 +
    (center1734.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1734]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1734 : work1734.theta.ok = true ∧
    work1734.jac.invOK = true ∧ acceptsUnitSq work1734.out = true := by decide +kernel

def cell1734 : CellCertificate where
  tauBall := tau1734
  contactCenter := center1734
  contactBall := contact1734
  work := work1734
  center_sq := center_sq1734
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1734.1
  jac_ok := checks1734.2.1
  accepted := checks1734.2.2

def tau1735 : RatBall :=
  ⟨⟨61/320, -97/320⟩, 3/640⟩
def center1735 : GaussianRat :=
  ⟨143309371/1000000000, -103995141/500000000⟩
def contact1735 : RatBall := localContactBall tau1735 center1735
def work1735 : RoundedTauEval :=
  evalTau precision tau1735 contact1735 logTwoBall

theorem center_sq1735 : (center1735.re : ℝ)^2 +
    (center1735.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1735]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1735 : work1735.theta.ok = true ∧
    work1735.jac.invOK = true ∧ acceptsUnitSq work1735.out = true := by decide +kernel

def cell1735 : CellCertificate where
  tauBall := tau1735
  contactCenter := center1735
  contactBall := contact1735
  work := work1735
  center_sq := center_sq1735
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1735.1
  jac_ok := checks1735.2.1
  accepted := checks1735.2.2

def cells : List CellCertificate := [cell1728, cell1729, cell1730, cell1731, cell1732, cell1733, cell1734, cell1735]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0216

end


