-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0156_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0156_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:07:08.711959+00:00
-- url     : https://prove2.me/theorems/f1a82788-f47a-4cc7-b676-7f67eea98884
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0156 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1248 : RatBall :=
  ⟨⟨-97/320, -81/320⟩, 3/640⟩
def center1248 : GaussianRat :=
  ⟨-108037641/500000000, -81137999/500000000⟩
def contact1248 : RatBall := localContactBall tau1248 center1248
def work1248 : RoundedTauEval :=
  evalTau precision tau1248 contact1248 logTwoBall

theorem center_sq1248 : (center1248.re : ℝ)^2 +
    (center1248.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1248]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1248 : work1248.theta.ok = true ∧
    work1248.jac.invOK = true ∧ acceptsUnitSq work1248.out = true := by decide +kernel

def cell1248 : CellCertificate where
  tauBall := tau1248
  contactCenter := center1248
  contactBall := contact1248
  work := work1248
  center_sq := center_sq1248
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1248.1
  jac_ok := checks1248.2.1
  accepted := checks1248.2.2

def tau1249 : RatBall :=
  ⟨⟨-21/64, -15/64⟩, 3/640⟩
def center1249 : GaussianRat :=
  ⟨-14403551/62500000, -14758413/100000000⟩
def contact1249 : RatBall := localContactBall tau1249 center1249
def work1249 : RoundedTauEval :=
  evalTau precision tau1249 contact1249 logTwoBall

theorem center_sq1249 : (center1249.re : ℝ)^2 +
    (center1249.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1249]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1249 : work1249.theta.ok = true ∧
    work1249.jac.invOK = true ∧ acceptsUnitSq work1249.out = true := by decide +kernel

def cell1249 : CellCertificate where
  tauBall := tau1249
  contactCenter := center1249
  contactBall := contact1249
  work := work1249
  center_sq := center_sq1249
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1249.1
  jac_ok := checks1249.2.1
  accepted := checks1249.2.2

def tau1250 : RatBall :=
  ⟨⟨-21/64, -73/320⟩, 3/640⟩
def center1250 : GaussianRat :=
  ⟨-229856067/1000000000, -5742857/40000000⟩
def contact1250 : RatBall := localContactBall tau1250 center1250
def work1250 : RoundedTauEval :=
  evalTau precision tau1250 contact1250 logTwoBall

theorem center_sq1250 : (center1250.re : ℝ)^2 +
    (center1250.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1250]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1250 : work1250.theta.ok = true ∧
    work1250.jac.invOK = true ∧ acceptsUnitSq work1250.out = true := by decide +kernel

def cell1250 : CellCertificate where
  tauBall := tau1250
  contactCenter := center1250
  contactBall := contact1250
  work := work1250
  center_sq := center_sq1250
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1250.1
  jac_ok := checks1250.2.1
  accepted := checks1250.2.2

def tau1251 : RatBall :=
  ⟨⟨-101/320, -79/320⟩, 3/640⟩
def center1251 : GaussianRat :=
  ⟨-111809453/500000000, -156912213/1000000000⟩
def contact1251 : RatBall := localContactBall tau1251 center1251
def work1251 : RoundedTauEval :=
  evalTau precision tau1251 contact1251 logTwoBall

theorem center_sq1251 : (center1251.re : ℝ)^2 +
    (center1251.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1251]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1251 : work1251.theta.ok = true ∧
    work1251.jac.invOK = true ∧ acceptsUnitSq work1251.out = true := by decide +kernel

def cell1251 : CellCertificate where
  tauBall := tau1251
  contactCenter := center1251
  contactBall := contact1251
  work := work1251
  center_sq := center_sq1251
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1251.1
  jac_ok := checks1251.2.1
  accepted := checks1251.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156


