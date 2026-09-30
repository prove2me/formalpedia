-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0205
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0205
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:56:02.051814+00:00
-- url     : https://prove2.me/theorems/fd805679-87aa-42c0-96e4-9c83c37e69f6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0205.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0205_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1644 : (center1644.re : ℝ)^2 +
    (center1644.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1644]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1644 : work1644.theta.ok = true ∧
    work1644.jac.invOK = true ∧ acceptsUnitSq work1644.out = true := by decide +kernel

def cell1644 : CellCertificate where
  tauBall := tau1644
  contactCenter := center1644
  contactBall := contact1644
  work := work1644
  center_sq := center_sq1644
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1644.1
  jac_ok := checks1644.2.1
  accepted := checks1644.2.2

def tau1645 : RatBall :=
  ⟨⟨9/64, -23/64⟩, 3/640⟩
def center1645 : GaussianRat :=
  ⟨889321/8000000, -254626433/1000000000⟩
def contact1645 : RatBall := localContactBall tau1645 center1645
def work1645 : RoundedTauEval :=
  evalTau precision tau1645 contact1645 logTwoBall

theorem center_sq1645 : (center1645.re : ℝ)^2 +
    (center1645.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1645]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1645 : work1645.theta.ok = true ∧
    work1645.jac.invOK = true ∧ acceptsUnitSq work1645.out = true := by decide +kernel

def cell1645 : CellCertificate where
  tauBall := tau1645
  contactCenter := center1645
  contactBall := contact1645
  work := work1645
  center_sq := center_sq1645
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1645.1
  jac_ok := checks1645.2.1
  accepted := checks1645.2.2

def tau1646 : RatBall :=
  ⟨⟨9/64, -113/320⟩, 3/640⟩
def center1646 : GaussianRat :=
  ⟨22120681/200000000, -249816993/1000000000⟩
def contact1646 : RatBall := localContactBall tau1646 center1646
def work1646 : RoundedTauEval :=
  evalTau precision tau1646 contact1646 logTwoBall

theorem center_sq1646 : (center1646.re : ℝ)^2 +
    (center1646.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1646]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1646 : work1646.theta.ok = true ∧
    work1646.jac.invOK = true ∧ acceptsUnitSq work1646.out = true := by decide +kernel

def cell1646 : CellCertificate where
  tauBall := tau1646
  contactCenter := center1646
  contactBall := contact1646
  work := work1646
  center_sq := center_sq1646
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1646.1
  jac_ok := checks1646.2.1
  accepted := checks1646.2.2

def tau1647 : RatBall :=
  ⟨⟨47/320, -113/320⟩, 3/640⟩
def center1647 : GaussianRat :=
  ⟨115394221/1000000000, -124626021/500000000⟩
def contact1647 : RatBall := localContactBall tau1647 center1647
def work1647 : RoundedTauEval :=
  evalTau precision tau1647 contact1647 logTwoBall

theorem center_sq1647 : (center1647.re : ℝ)^2 +
    (center1647.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1647]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1647 : work1647.theta.ok = true ∧
    work1647.jac.invOK = true ∧ acceptsUnitSq work1647.out = true := by decide +kernel

def cell1647 : CellCertificate where
  tauBall := tau1647
  contactCenter := center1647
  contactBall := contact1647
  work := work1647
  center_sq := center_sq1647
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1647.1
  jac_ok := checks1647.2.1
  accepted := checks1647.2.2

def cells : List CellCertificate := [cell1640, cell1641, cell1642, cell1643, cell1644, cell1645, cell1646, cell1647]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205


