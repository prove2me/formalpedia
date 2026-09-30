-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0080
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0080
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:30:43.2934+00:00
-- url     : https://prove2.me/theorems/65d1b18d-08d7-457f-a878-5951b85d73aa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0080` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0080` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0080` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0080 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0080.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0080 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0080

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0640 : RatBall :=
  ⟨⟨5/32, -37/160⟩, 3/320⟩
def center0640 : GaussianRat :=
  ⟨113439149/1000000000, -158939613/1000000000⟩
def contact0640 : RatBall := localContactBall tau0640 center0640
def work0640 : RoundedTauEval :=
  evalTau precision tau0640 contact0640 logTwoBall

theorem center_sq0640 : (center0640.re : ℝ)^2 +
    (center0640.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0640]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0640 : work0640.theta.ok = true ∧
    work0640.jac.invOK = true ∧ acceptsUnitSq work0640.out = true := by decide +kernel

def cell0640 : CellCertificate where
  tauBall := tau0640
  contactCenter := center0640
  contactBall := contact0640
  work := work0640
  center_sq := center_sq0640
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0640.1
  jac_ok := checks0640.2.1
  accepted := checks0640.2.2

def tau0641 : RatBall :=
  ⟨⟨27/160, -37/160⟩, 3/320⟩
def center0641 : GaussianRat :=
  ⟨122297939/1000000000, -158228017/1000000000⟩
def contact0641 : RatBall := localContactBall tau0641 center0641
def work0641 : RoundedTauEval :=
  evalTau precision tau0641 contact0641 logTwoBall

theorem center_sq0641 : (center0641.re : ℝ)^2 +
    (center0641.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0641]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0641 : work0641.theta.ok = true ∧
    work0641.jac.invOK = true ∧ acceptsUnitSq work0641.out = true := by decide +kernel

def cell0641 : CellCertificate where
  tauBall := tau0641
  contactCenter := center0641
  contactBall := contact0641
  work := work0641
  center_sq := center_sq0641
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0641.1
  jac_ok := checks0641.2.1
  accepted := checks0641.2.2

def tau0642 : RatBall :=
  ⟨⟨29/160, -39/160⟩, 3/320⟩
def center0642 : GaussianRat :=
  ⟨131916433/1000000000, -83139101/500000000⟩
def contact0642 : RatBall := localContactBall tau0642 center0642
def work0642 : RoundedTauEval :=
  evalTau precision tau0642 contact0642 logTwoBall

theorem center_sq0642 : (center0642.re : ℝ)^2 +
    (center0642.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0642]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0642 : work0642.theta.ok = true ∧
    work0642.jac.invOK = true ∧ acceptsUnitSq work0642.out = true := by decide +kernel

def cell0642 : CellCertificate where
  tauBall := tau0642
  contactCenter := center0642
  contactBall := contact0642
  work := work0642
  center_sq := center_sq0642
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0642.1
  jac_ok := checks0642.2.1
  accepted := checks0642.2.2

def tau0643 : RatBall :=
  ⟨⟨31/160, -39/160⟩, 3/320⟩
def center0643 : GaussianRat :=
  ⟨2814451/20000000, -33084071/200000000⟩
def contact0643 : RatBall := localContactBall tau0643 center0643
def work0643 : RoundedTauEval :=
  evalTau precision tau0643 contact0643 logTwoBall

theorem center_sq0643 : (center0643.re : ℝ)^2 +
    (center0643.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0643]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0643 : work0643.theta.ok = true ∧
    work0643.jac.invOK = true ∧ acceptsUnitSq work0643.out = true := by decide +kernel

def cell0643 : CellCertificate where
  tauBall := tau0643
  contactCenter := center0643
  contactBall := contact0643
  work := work0643
  center_sq := center_sq0643
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0643.1
  jac_ok := checks0643.2.1
  accepted := checks0643.2.2

def tau0644 : RatBall :=
  ⟨⟨29/160, -37/160⟩, 3/320⟩
def center0644 : GaussianRat :=
  ⟨8194291/62500000, -7873457/50000000⟩
def contact0644 : RatBall := localContactBall tau0644 center0644
def work0644 : RoundedTauEval :=
  evalTau precision tau0644 contact0644 logTwoBall

theorem center_sq0644 : (center0644.re : ℝ)^2 +
    (center0644.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0644]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0644 : work0644.theta.ok = true ∧
    work0644.jac.invOK = true ∧ acceptsUnitSq work0644.out = true := by decide +kernel

def cell0644 : CellCertificate where
  tauBall := tau0644
  contactCenter := center0644
  contactBall := contact0644
  work := work0644
  center_sq := center_sq0644
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0644.1
  jac_ok := checks0644.2.1
  accepted := checks0644.2.2

def tau0645 : RatBall :=
  ⟨⟨31/160, -37/160⟩, 3/320⟩
def center0645 : GaussianRat :=
  ⟨139868391/1000000000, -78332251/500000000⟩
def contact0645 : RatBall := localContactBall tau0645 center0645
def work0645 : RoundedTauEval :=
  evalTau precision tau0645 contact0645 logTwoBall

theorem center_sq0645 : (center0645.re : ℝ)^2 +
    (center0645.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0645]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0645 : work0645.theta.ok = true ∧
    work0645.jac.invOK = true ∧ acceptsUnitSq work0645.out = true := by decide +kernel

def cell0645 : CellCertificate where
  tauBall := tau0645
  contactCenter := center0645
  contactBall := contact0645
  work := work0645
  center_sq := center_sq0645
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0645.1
  jac_ok := checks0645.2.1
  accepted := checks0645.2.2

def tau0646 : RatBall :=
  ⟨⟨33/160, -9/32⟩, 3/320⟩
def center0646 : GaussianRat :=
  ⟨9532907/62500000, -95448491/500000000⟩
def contact0646 : RatBall := localContactBall tau0646 center0646
def work0646 : RoundedTauEval :=
  evalTau precision tau0646 contact0646 logTwoBall

theorem center_sq0646 : (center0646.re : ℝ)^2 +
    (center0646.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0646]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0646 : work0646.theta.ok = true ∧
    work0646.jac.invOK = true ∧ acceptsUnitSq work0646.out = true := by decide +kernel

def cell0646 : CellCertificate where
  tauBall := tau0646
  contactCenter := center0646
  contactBall := contact0646
  work := work0646
  center_sq := center_sq0646
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0646.1
  jac_ok := checks0646.2.1
  accepted := checks0646.2.2

def tau0647 : RatBall :=
  ⟨⟨7/32, -9/32⟩, 3/320⟩
def center0647 : GaussianRat :=
  ⟨32272717/200000000, -189759799/1000000000⟩
def contact0647 : RatBall := localContactBall tau0647 center0647
def work0647 : RoundedTauEval :=
  evalTau precision tau0647 contact0647 logTwoBall

theorem center_sq0647 : (center0647.re : ℝ)^2 +
    (center0647.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0647]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0647 : work0647.theta.ok = true ∧
    work0647.jac.invOK = true ∧ acceptsUnitSq work0647.out = true := by decide +kernel

def cell0647 : CellCertificate where
  tauBall := tau0647
  contactCenter := center0647
  contactBall := contact0647
  work := work0647
  center_sq := center_sq0647
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0647.1
  jac_ok := checks0647.2.1
  accepted := checks0647.2.2

def cells : List CellCertificate := [cell0640, cell0641, cell0642, cell0643, cell0644, cell0645, cell0646, cell0647]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0080

end


