-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0236_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0236_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:15:38.65902+00:00
-- url     : https://prove2.me/theorems/f5f77879-a5cc-4f92-97b0-12f26302fa3f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0236 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0236_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1890 : RoundedTauEval :=
  evalTau precision tau1890 contact1890 logTwoBall

theorem center_sq1890 : (center1890.re : ℝ)^2 +
    (center1890.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1890]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1890 : work1890.theta.ok = true ∧
    work1890.jac.invOK = true ∧ acceptsUnitSq work1890.out = true := by decide +kernel

def cell1890 : CellCertificate where
  tauBall := tau1890
  contactCenter := center1890
  contactBall := contact1890
  work := work1890
  center_sq := center_sq1890
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1890.1
  jac_ok := checks1890.2.1
  accepted := checks1890.2.2

def tau1891 : RatBall :=
  ⟨⟨-21/64, 73/320⟩, 3/640⟩
def center1891 : GaussianRat :=
  ⟨-229856067/1000000000, 5742857/40000000⟩
def contact1891 : RatBall := localContactBall tau1891 center1891
def work1891 : RoundedTauEval :=
  evalTau precision tau1891 contact1891 logTwoBall

theorem center_sq1891 : (center1891.re : ℝ)^2 +
    (center1891.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1891]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1891 : work1891.theta.ok = true ∧
    work1891.jac.invOK = true ∧ acceptsUnitSq work1891.out = true := by decide +kernel

def cell1891 : CellCertificate where
  tauBall := tau1891
  contactCenter := center1891
  contactBall := contact1891
  work := work1891
  center_sq := center_sq1891
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1891.1
  jac_ok := checks1891.2.1
  accepted := checks1891.2.2

def tau1892 : RatBall :=
  ⟨⟨-21/64, 15/64⟩, 3/640⟩
def center1892 : GaussianRat :=
  ⟨-14403551/62500000, 14758413/100000000⟩
def contact1892 : RatBall := localContactBall tau1892 center1892
def work1892 : RoundedTauEval :=
  evalTau precision tau1892 contact1892 logTwoBall

theorem center_sq1892 : (center1892.re : ℝ)^2 +
    (center1892.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1892]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1892 : work1892.theta.ok = true ∧
    work1892.jac.invOK = true ∧ acceptsUnitSq work1892.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236


