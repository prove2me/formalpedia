-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0217_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0217_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:22:27.399474+00:00
-- url     : https://prove2.me/theorems/0b6e9ee3-8575-4788-b970-ffaf12a8fdcc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0217 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1736 : RatBall :=
  ⟨⟨63/320, -97/320⟩, 3/640⟩
def center1736 : GaussianRat :=
  ⟨147826489/1000000000, -2592583/12500000⟩
def contact1736 : RatBall := localContactBall tau1736 center1736
def work1736 : RoundedTauEval :=
  evalTau precision tau1736 contact1736 logTwoBall

theorem center_sq1736 : (center1736.re : ℝ)^2 +
    (center1736.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1736]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1736 : work1736.theta.ok = true ∧
    work1736.jac.invOK = true ∧ acceptsUnitSq work1736.out = true := by decide +kernel

def cell1736 : CellCertificate where
  tauBall := tau1736
  contactCenter := center1736
  contactBall := contact1736
  work := work1736
  center_sq := center_sq1736
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1736.1
  jac_ok := checks1736.2.1
  accepted := checks1736.2.2

def tau1737 : RatBall :=
  ⟨⟨13/64, -107/320⟩, 3/640⟩
def center1737 : GaussianRat :=
  ⟨77788111/500000000, -229460827/1000000000⟩
def contact1737 : RatBall := localContactBall tau1737 center1737
def work1737 : RoundedTauEval :=
  evalTau precision tau1737 contact1737 logTwoBall

theorem center_sq1737 : (center1737.re : ℝ)^2 +
    (center1737.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1737]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1737 : work1737.theta.ok = true ∧
    work1737.jac.invOK = true ∧ acceptsUnitSq work1737.out = true := by decide +kernel

def cell1737 : CellCertificate where
  tauBall := tau1737
  contactCenter := center1737
  contactBall := contact1737
  work := work1737
  center_sq := center_sq1737
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1737.1
  jac_ok := checks1737.2.1
  accepted := checks1737.2.2

def tau1738 : RatBall :=
  ⟨⟨67/320, -107/320⟩, 3/640⟩
def center1738 : GaussianRat :=
  ⟨160137389/1000000000, -228757569/1000000000⟩
def contact1738 : RatBall := localContactBall tau1738 center1738
def work1738 : RoundedTauEval :=
  evalTau precision tau1738 contact1738 logTwoBall

theorem center_sq1738 : (center1738.re : ℝ)^2 +
    (center1738.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1738]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1738 : work1738.theta.ok = true ∧
    work1738.jac.invOK = true ∧ acceptsUnitSq work1738.out = true := by decide +kernel

def cell1738 : CellCertificate where
  tauBall := tau1738
  contactCenter := center1738
  contactBall := contact1738
  work := work1738
  center_sq := center_sq1738
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1738.1
  jac_ok := checks1738.2.1
  accepted := checks1738.2.2

def tau1739 : RatBall :=
  ⟨⟨13/64, -21/64⟩, 3/640⟩
def center1739 : GaussianRat :=
  ⟨30978099/200000000, -224898511/1000000000⟩
def contact1739 : RatBall := localContactBall tau1739 center1739
def work1739 : RoundedTauEval :=
  evalTau precision tau1739 contact1739 logTwoBall

theorem center_sq1739 : (center1739.re : ℝ)^2 +
    (center1739.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1739]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1739 : work1739.theta.ok = true ∧
    work1739.jac.invOK = true ∧ acceptsUnitSq work1739.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217


