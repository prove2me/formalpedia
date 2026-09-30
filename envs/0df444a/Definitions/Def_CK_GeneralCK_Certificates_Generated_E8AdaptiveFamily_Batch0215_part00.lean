-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0215_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0215_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:41:40.724279+00:00
-- url     : https://prove2.me/theorems/35834564-e7e9-4783-81dc-fc06b8ae4742
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0215 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1720 : RatBall :=
  ⟨⟨11/64, -101/320⟩, 3/640⟩
def center1720 : GaussianRat :=
  ⟨3268749/25000000, -54706193/250000000⟩
def contact1720 : RatBall := localContactBall tau1720 center1720
def work1720 : RoundedTauEval :=
  evalTau precision tau1720 contact1720 logTwoBall

theorem center_sq1720 : (center1720.re : ℝ)^2 +
    (center1720.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1720]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1720 : work1720.theta.ok = true ∧
    work1720.jac.invOK = true ∧ acceptsUnitSq work1720.out = true := by decide +kernel

def cell1720 : CellCertificate where
  tauBall := tau1720
  contactCenter := center1720
  contactBall := contact1720
  work := work1720
  center_sq := center_sq1720
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1720.1
  jac_ok := checks1720.2.1
  accepted := checks1720.2.2

def tau1721 : RatBall :=
  ⟨⟨57/320, -103/320⟩, 3/640⟩
def center1721 : GaussianRat :=
  ⟨135931497/1000000000, -55713833/250000000⟩
def contact1721 : RatBall := localContactBall tau1721 center1721
def work1721 : RoundedTauEval :=
  evalTau precision tau1721 contact1721 logTwoBall

theorem center_sq1721 : (center1721.re : ℝ)^2 +
    (center1721.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1721]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1721 : work1721.theta.ok = true ∧
    work1721.jac.invOK = true ∧ acceptsUnitSq work1721.out = true := by decide +kernel

def cell1721 : CellCertificate where
  tauBall := tau1721
  contactCenter := center1721
  contactBall := contact1721
  work := work1721
  center_sq := center_sq1721
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1721.1
  jac_ok := checks1721.2.1
  accepted := checks1721.2.2

def tau1722 : RatBall :=
  ⟨⟨59/320, -103/320⟩, 3/640⟩
def center1722 : GaussianRat :=
  ⟨140529903/1000000000, -222254637/1000000000⟩
def contact1722 : RatBall := localContactBall tau1722 center1722
def work1722 : RoundedTauEval :=
  evalTau precision tau1722 contact1722 logTwoBall

theorem center_sq1722 : (center1722.re : ℝ)^2 +
    (center1722.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1722]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1722 : work1722.theta.ok = true ∧
    work1722.jac.invOK = true ∧ acceptsUnitSq work1722.out = true := by decide +kernel

def cell1722 : CellCertificate where
  tauBall := tau1722
  contactCenter := center1722
  contactBall := contact1722
  work := work1722
  center_sq := center_sq1722
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1722.1
  jac_ok := checks1722.2.1
  accepted := checks1722.2.2

def tau1723 : RatBall :=
  ⟨⟨57/320, -101/320⟩, 3/640⟩
def center1723 : GaussianRat :=
  ⟨135347471/1000000000, -43651451/200000000⟩
def contact1723 : RatBall := localContactBall tau1723 center1723
def work1723 : RoundedTauEval :=
  evalTau precision tau1723 contact1723 logTwoBall

theorem center_sq1723 : (center1723.re : ℝ)^2 +
    (center1723.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1723]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1723 : work1723.theta.ok = true ∧
    work1723.jac.invOK = true ∧ acceptsUnitSq work1723.out = true := by decide +kernel

def cell1723 : CellCertificate where
  tauBall := tau1723
  contactCenter := center1723
  contactBall := contact1723
  work := work1723
  center_sq := center_sq1723
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1723.1
  jac_ok := checks1723.2.1
  accepted := checks1723.2.2

def tau1724 : RatBall :=
  ⟨⟨59/320, -101/320⟩, 3/640⟩
def center1724 : GaussianRat :=
  ⟨27985801/200000000, -54418229/250000000⟩
def contact1724 : RatBall := localContactBall tau1724 center1724

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215


