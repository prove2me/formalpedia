-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0189_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0189_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:13:47.10154+00:00
-- url     : https://prove2.me/theorems/84e21089-22ed-478e-b4a6-1f923072facb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0189 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0189_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1514 : RoundedTauEval :=
  evalTau precision tau1514 contact1514 logTwoBall

theorem center_sq1514 : (center1514.re : ℝ)^2 +
    (center1514.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1514]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1514 : work1514.theta.ok = true ∧
    work1514.jac.invOK = true ∧ acceptsUnitSq work1514.out = true := by decide +kernel

def cell1514 : CellCertificate where
  tauBall := tau1514
  contactCenter := center1514
  contactBall := contact1514
  work := work1514
  center_sq := center_sq1514
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1514.1
  jac_ok := checks1514.2.1
  accepted := checks1514.2.2

def tau1515 : RatBall :=
  ⟨⟨-9/320, -113/320⟩, 3/640⟩
def center1515 : GaussianRat :=
  ⟨-22380501/1000000000, -127986203/500000000⟩
def contact1515 : RatBall := localContactBall tau1515 center1515
def work1515 : RoundedTauEval :=
  evalTau precision tau1515 contact1515 logTwoBall

theorem center_sq1515 : (center1515.re : ℝ)^2 +
    (center1515.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1515]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1515 : work1515.theta.ok = true ∧
    work1515.jac.invOK = true ∧ acceptsUnitSq work1515.out = true := by decide +kernel

def cell1515 : CellCertificate where
  tauBall := tau1515
  contactCenter := center1515
  contactBall := contact1515
  work := work1515
  center_sq := center_sq1515
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1515.1
  jac_ok := checks1515.2.1
  accepted := checks1515.2.2

def tau1516 : RatBall :=
  ⟨⟨-7/320, -119/320⟩, 3/640⟩
def center1516 : GaussianRat :=
  ⟨-3539231/200000000, -67777837/250000000⟩
def contact1516 : RatBall := localContactBall tau1516 center1516
def work1516 : RoundedTauEval :=
  evalTau precision tau1516 contact1516 logTwoBall

theorem center_sq1516 : (center1516.re : ℝ)^2 +
    (center1516.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1516]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1516 : work1516.theta.ok = true ∧
    work1516.jac.invOK = true ∧ acceptsUnitSq work1516.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189


