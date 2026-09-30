-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0212
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0212
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:42:51.985991+00:00
-- url     : https://prove2.me/theorems/ccdef379-5b7c-4044-b865-be676b8427cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0212.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0212_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1700 : RoundedTauEval :=
  evalTau precision tau1700 contact1700 logTwoBall

theorem center_sq1700 : (center1700.re : ℝ)^2 +
    (center1700.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1700]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1700 : work1700.theta.ok = true ∧
    work1700.jac.invOK = true ∧ acceptsUnitSq work1700.out = true := by decide +kernel

def cell1700 : CellCertificate where
  tauBall := tau1700
  contactCenter := center1700
  contactBall := contact1700
  work := work1700
  center_sq := center_sq1700
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1700.1
  jac_ok := checks1700.2.1
  accepted := checks1700.2.2

def tau1701 : RatBall :=
  ⟨⟨57/320, -109/320⟩, 3/640⟩
def center1701 : GaussianRat :=
  ⟨137782813/1000000000, -5918871/25000000⟩
def contact1701 : RatBall := localContactBall tau1701 center1701
def work1701 : RoundedTauEval :=
  evalTau precision tau1701 contact1701 logTwoBall

theorem center_sq1701 : (center1701.re : ℝ)^2 +
    (center1701.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1701]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1701 : work1701.theta.ok = true ∧
    work1701.jac.invOK = true ∧ acceptsUnitSq work1701.out = true := by decide +kernel

def cell1701 : CellCertificate where
  tauBall := tau1701
  contactCenter := center1701
  contactBall := contact1701
  work := work1701
  center_sq := center_sq1701
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1701.1
  jac_ok := checks1701.2.1
  accepted := checks1701.2.2

def tau1702 : RatBall :=
  ⟨⟨59/320, -109/320⟩, 3/640⟩
def center1702 : GaussianRat :=
  ⟨71217211/500000000, -236102993/1000000000⟩
def contact1702 : RatBall := localContactBall tau1702 center1702
def work1702 : RoundedTauEval :=
  evalTau precision tau1702 contact1702 logTwoBall

theorem center_sq1702 : (center1702.re : ℝ)^2 +
    (center1702.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1702]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1702 : work1702.theta.ok = true ∧
    work1702.jac.invOK = true ∧ acceptsUnitSq work1702.out = true := by decide +kernel

def cell1702 : CellCertificate where
  tauBall := tau1702
  contactCenter := center1702
  contactBall := contact1702
  work := work1702
  center_sq := center_sq1702
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1702.1
  jac_ok := checks1702.2.1
  accepted := checks1702.2.2

def tau1703 : RatBall :=
  ⟨⟨61/320, -109/320⟩, 3/640⟩
def center1703 : GaussianRat :=
  ⟨147068213/1000000000, -14714559/62500000⟩
def contact1703 : RatBall := localContactBall tau1703 center1703
def work1703 : RoundedTauEval :=
  evalTau precision tau1703 contact1703 logTwoBall

theorem center_sq1703 : (center1703.re : ℝ)^2 +
    (center1703.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1703]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1703 : work1703.theta.ok = true ∧
    work1703.jac.invOK = true ∧ acceptsUnitSq work1703.out = true := by decide +kernel

def cell1703 : CellCertificate where
  tauBall := tau1703
  contactCenter := center1703
  contactBall := contact1703
  work := work1703
  center_sq := center_sq1703
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1703.1
  jac_ok := checks1703.2.1
  accepted := checks1703.2.2

def cells : List CellCertificate := [cell1696, cell1697, cell1698, cell1699, cell1700, cell1701, cell1702, cell1703]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212


