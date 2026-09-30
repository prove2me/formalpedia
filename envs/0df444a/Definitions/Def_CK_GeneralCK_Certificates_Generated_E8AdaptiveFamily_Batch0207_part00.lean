-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0207_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0207_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:21:06.149542+00:00
-- url     : https://prove2.me/theorems/cac80879-99ae-41e2-909a-6bfa9fdc48a7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0207 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1656 : RatBall :=
  ⟨⟨39/320, -111/320⟩, 3/640⟩
def center1656 : GaussianRat :=
  ⟨11957763/125000000, -15409367/62500000⟩
def contact1656 : RatBall := localContactBall tau1656 center1656
def work1656 : RoundedTauEval :=
  evalTau precision tau1656 contact1656 logTwoBall

theorem center_sq1656 : (center1656.re : ℝ)^2 +
    (center1656.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1656]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1656 : work1656.theta.ok = true ∧
    work1656.jac.invOK = true ∧ acceptsUnitSq work1656.out = true := by decide +kernel

def cell1656 : CellCertificate where
  tauBall := tau1656
  contactCenter := center1656
  contactBall := contact1656
  work := work1656
  center_sq := center_sq1656
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1656.1
  jac_ok := checks1656.2.1
  accepted := checks1656.2.2

def tau1657 : RatBall :=
  ⟨⟨37/320, -109/320⟩, 3/640⟩
def center1657 : GaussianRat :=
  ⟨45195779/500000000, -121096227/500000000⟩
def contact1657 : RatBall := localContactBall tau1657 center1657
def work1657 : RoundedTauEval :=
  evalTau precision tau1657 contact1657 logTwoBall

theorem center_sq1657 : (center1657.re : ℝ)^2 +
    (center1657.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1657]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1657 : work1657.theta.ok = true ∧
    work1657.jac.invOK = true ∧ acceptsUnitSq work1657.out = true := by decide +kernel

def cell1657 : CellCertificate where
  tauBall := tau1657
  contactCenter := center1657
  contactBall := contact1657
  work := work1657
  center_sq := center_sq1657
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1657.1
  jac_ok := checks1657.2.1
  accepted := checks1657.2.2

def tau1658 : RatBall :=
  ⟨⟨39/320, -109/320⟩, 3/640⟩
def center1658 : GaussianRat :=
  ⟨47597289/500000000, -241742219/1000000000⟩
def contact1658 : RatBall := localContactBall tau1658 center1658
def work1658 : RoundedTauEval :=
  evalTau precision tau1658 contact1658 logTwoBall

theorem center_sq1658 : (center1658.re : ℝ)^2 +
    (center1658.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1658]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1658 : work1658.theta.ok = true ∧
    work1658.jac.invOK = true ∧ acceptsUnitSq work1658.out = true := by decide +kernel

def cell1658 : CellCertificate where
  tauBall := tau1658
  contactCenter := center1658
  contactBall := contact1658
  work := work1658
  center_sq := center_sq1658
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1658.1
  jac_ok := checks1658.2.1
  accepted := checks1658.2.2

def tau1659 : RatBall :=
  ⟨⟨37/320, -107/320⟩, 3/640⟩
def center1659 : GaussianRat :=
  ⟨22489569/250000000, -47478823/200000000⟩
def contact1659 : RatBall := localContactBall tau1659 center1659
def work1659 : RoundedTauEval :=
  evalTau precision tau1659 contact1659 logTwoBall

theorem center_sq1659 : (center1659.re : ℝ)^2 +
    (center1659.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1659]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1659 : work1659.theta.ok = true ∧
    work1659.jac.invOK = true ∧ acceptsUnitSq work1659.out = true := by decide +kernel

def cell1659 : CellCertificate where
  tauBall := tau1659
  contactCenter := center1659
  contactBall := contact1659
  work := work1659
  center_sq := center_sq1659
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1659.1
  jac_ok := checks1659.2.1
  accepted := checks1659.2.2

def tau1660 : RatBall :=
  ⟨⟨39/320, -107/320⟩, 3/640⟩
def center1660 : GaussianRat :=
  ⟨23684951/250000000, -1184781/5000000⟩
def contact1660 : RatBall := localContactBall tau1660 center1660
def work1660 : RoundedTauEval :=
  evalTau precision tau1660 contact1660 logTwoBall

theorem center_sq1660 : (center1660.re : ℝ)^2 +
    (center1660.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1660]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1660 : work1660.theta.ok = true ∧
    work1660.jac.invOK = true ∧ acceptsUnitSq work1660.out = true := by decide +kernel

def cell1660 : CellCertificate where
  tauBall := tau1660
  contactCenter := center1660
  contactBall := contact1660
  work := work1660
  center_sq := center_sq1660
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1660.1
  jac_ok := checks1660.2.1
  accepted := checks1660.2.2

def tau1661 : RatBall :=
  ⟨⟨37/320, -21/64⟩, 3/640⟩
def center1661 : GaussianRat :=
  ⟨89536891/1000000000, -116308561/500000000⟩
def contact1661 : RatBall := localContactBall tau1661 center1661
def work1661 : RoundedTauEval :=
  evalTau precision tau1661 contact1661 logTwoBall

theorem center_sq1661 : (center1661.re : ℝ)^2 +
    (center1661.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1661]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1661 : work1661.theta.ok = true ∧
    work1661.jac.invOK = true ∧ acceptsUnitSq work1661.out = true := by decide +kernel

def cell1661 : CellCertificate where
  tauBall := tau1661
  contactCenter := center1661
  contactBall := contact1661
  work := work1661
  center_sq := center_sq1661
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1661.1
  jac_ok := checks1661.2.1
  accepted := checks1661.2.2

def tau1662 : RatBall :=
  ⟨⟨39/320, -21/64⟩, 3/640⟩
def center1662 : GaussianRat :=
  ⟨94297493/1000000000, -185753/800000⟩
def contact1662 : RatBall := localContactBall tau1662 center1662

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207


