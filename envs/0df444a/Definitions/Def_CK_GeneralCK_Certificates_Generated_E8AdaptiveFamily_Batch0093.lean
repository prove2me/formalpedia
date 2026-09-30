-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0093
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0093
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:04:54.28551+00:00
-- url     : https://prove2.me/theorems/bccbad8b-ae72-4e8c-a51e-d8f0023b1858
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0093` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0093` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0093` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0093 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0093.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0093 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0093

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0744 : RatBall :=
  ⟨⟨57/160, -23/160⟩, 3/320⟩
def center0744 : GaussianRat :=
  ⟨30133041/125000000, -17660441/200000000⟩
def contact0744 : RatBall := localContactBall tau0744 center0744
def work0744 : RoundedTauEval :=
  evalTau precision tau0744 contact0744 logTwoBall

theorem center_sq0744 : (center0744.re : ℝ)^2 +
    (center0744.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0744]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0744 : work0744.theta.ok = true ∧
    work0744.jac.invOK = true ∧ acceptsUnitSq work0744.out = true := by decide +kernel

def cell0744 : CellCertificate where
  tauBall := tau0744
  contactCenter := center0744
  contactBall := contact0744
  work := work0744
  center_sq := center_sq0744
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0744.1
  jac_ok := checks0744.2.1
  accepted := checks0744.2.2

def tau0745 : RatBall :=
  ⟨⟨59/160, -23/160⟩, 3/320⟩
def center0745 : GaussianRat :=
  ⟨248760621/1000000000, -43775671/500000000⟩
def contact0745 : RatBall := localContactBall tau0745 center0745
def work0745 : RoundedTauEval :=
  evalTau precision tau0745 contact0745 logTwoBall

theorem center_sq0745 : (center0745.re : ℝ)^2 +
    (center0745.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0745]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0745 : work0745.theta.ok = true ∧
    work0745.jac.invOK = true ∧ acceptsUnitSq work0745.out = true := by decide +kernel

def cell0745 : CellCertificate where
  tauBall := tau0745
  contactCenter := center0745
  contactBall := contact0745
  work := work0745
  center_sq := center_sq0745
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0745.1
  jac_ok := checks0745.2.1
  accepted := checks0745.2.2

def tau0746 : RatBall :=
  ⟨⟨57/160, -21/160⟩, 3/320⟩
def center0746 : GaussianRat :=
  ⟨120177071/500000000, -16115617/200000000⟩
def contact0746 : RatBall := localContactBall tau0746 center0746
def work0746 : RoundedTauEval :=
  evalTau precision tau0746 contact0746 logTwoBall

theorem center_sq0746 : (center0746.re : ℝ)^2 +
    (center0746.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0746]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0746 : work0746.theta.ok = true ∧
    work0746.jac.invOK = true ∧ acceptsUnitSq work0746.out = true := by decide +kernel

def cell0746 : CellCertificate where
  tauBall := tau0746
  contactCenter := center0746
  contactBall := contact0746
  work := work0746
  center_sq := center_sq0746
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0746.1
  jac_ok := checks0746.2.1
  accepted := checks0746.2.2

def tau0747 : RatBall :=
  ⟨⟨59/160, -21/160⟩, 3/320⟩
def center0747 : GaussianRat :=
  ⟨124018963/500000000, -79895753/1000000000⟩
def contact0747 : RatBall := localContactBall tau0747 center0747
def work0747 : RoundedTauEval :=
  evalTau precision tau0747 contact0747 logTwoBall

theorem center_sq0747 : (center0747.re : ℝ)^2 +
    (center0747.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0747]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0747 : work0747.theta.ok = true ∧
    work0747.jac.invOK = true ∧ acceptsUnitSq work0747.out = true := by decide +kernel

def cell0747 : CellCertificate where
  tauBall := tau0747
  contactCenter := center0747
  contactBall := contact0747
  work := work0747
  center_sq := center_sq0747
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0747.1
  jac_ok := checks0747.2.1
  accepted := checks0747.2.2

def tau0748 : RatBall :=
  ⟨⟨61/160, -23/160⟩, 3/320⟩
def center0748 : GaussianRat :=
  ⟨64096843/250000000, -86787913/1000000000⟩
def contact0748 : RatBall := localContactBall tau0748 center0748
def work0748 : RoundedTauEval :=
  evalTau precision tau0748 contact0748 logTwoBall

theorem center_sq0748 : (center0748.re : ℝ)^2 +
    (center0748.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0748]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0748 : work0748.theta.ok = true ∧
    work0748.jac.invOK = true ∧ acceptsUnitSq work0748.out = true := by decide +kernel

def cell0748 : CellCertificate where
  tauBall := tau0748
  contactCenter := center0748
  contactBall := contact0748
  work := work0748
  center_sq := center_sq0748
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0748.1
  jac_ok := checks0748.2.1
  accepted := checks0748.2.2

def tau0749 : RatBall :=
  ⟨⟨61/160, -21/160⟩, 3/320⟩
def center0749 : GaussianRat :=
  ⟨15978319/62500000, -79201909/1000000000⟩
def contact0749 : RatBall := localContactBall tau0749 center0749
def work0749 : RoundedTauEval :=
  evalTau precision tau0749 contact0749 logTwoBall

theorem center_sq0749 : (center0749.re : ℝ)^2 +
    (center0749.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0749]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0749 : work0749.theta.ok = true ∧
    work0749.jac.invOK = true ∧ acceptsUnitSq work0749.out = true := by decide +kernel

def cell0749 : CellCertificate where
  tauBall := tau0749
  contactCenter := center0749
  contactBall := contact0749
  work := work0749
  center_sq := center_sq0749
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0749.1
  jac_ok := checks0749.2.1
  accepted := checks0749.2.2

def tau0750 : RatBall :=
  ⟨⟨57/160, -19/160⟩, 3/320⟩
def center0750 : GaussianRat :=
  ⟨239711471/1000000000, -72866371/1000000000⟩
def contact0750 : RatBall := localContactBall tau0750 center0750
def work0750 : RoundedTauEval :=
  evalTau precision tau0750 contact0750 logTwoBall

theorem center_sq0750 : (center0750.re : ℝ)^2 +
    (center0750.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0750]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0750 : work0750.theta.ok = true ∧
    work0750.jac.invOK = true ∧ acceptsUnitSq work0750.out = true := by decide +kernel

def cell0750 : CellCertificate where
  tauBall := tau0750
  contactCenter := center0750
  contactBall := contact0750
  work := work0750
  center_sq := center_sq0750
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0750.1
  jac_ok := checks0750.2.1
  accepted := checks0750.2.2

def tau0751 : RatBall :=
  ⟨⟨59/160, -19/160⟩, 3/320⟩
def center0751 : GaussianRat :=
  ⟨247383851/1000000000, -72251673/1000000000⟩
def contact0751 : RatBall := localContactBall tau0751 center0751
def work0751 : RoundedTauEval :=
  evalTau precision tau0751 contact0751 logTwoBall

theorem center_sq0751 : (center0751.re : ℝ)^2 +
    (center0751.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0751]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0751 : work0751.theta.ok = true ∧
    work0751.jac.invOK = true ∧ acceptsUnitSq work0751.out = true := by decide +kernel

def cell0751 : CellCertificate where
  tauBall := tau0751
  contactCenter := center0751
  contactBall := contact0751
  work := work0751
  center_sq := center_sq0751
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0751.1
  jac_ok := checks0751.2.1
  accepted := checks0751.2.2

def cells : List CellCertificate := [cell0744, cell0745, cell0746, cell0747, cell0748, cell0749, cell0750, cell0751]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0093

end


