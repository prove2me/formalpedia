-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0238_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0238_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:12:39.968846+00:00
-- url     : https://prove2.me/theorems/924cf543-7a97-42b7-8698-250f42cd1114
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0238 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1904 : RatBall :=
  ⟨⟨-99/320, 81/320⟩, 3/640⟩
def center1904 : GaussianRat :=
  ⟨-55044701/250000000, 161633449/1000000000⟩
def contact1904 : RatBall := localContactBall tau1904 center1904
def work1904 : RoundedTauEval :=
  evalTau precision tau1904 contact1904 logTwoBall

theorem center_sq1904 : (center1904.re : ℝ)^2 +
    (center1904.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1904]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1904 : work1904.theta.ok = true ∧
    work1904.jac.invOK = true ∧ acceptsUnitSq work1904.out = true := by decide +kernel

def cell1904 : CellCertificate where
  tauBall := tau1904
  contactCenter := center1904
  contactBall := contact1904
  work := work1904
  center_sq := center_sq1904
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1904.1
  jac_ok := checks1904.2.1
  accepted := checks1904.2.2

def tau1905 : RatBall :=
  ⟨⟨-97/320, 81/320⟩, 3/640⟩
def center1905 : GaussianRat :=
  ⟨-108037641/500000000, 81137999/500000000⟩
def contact1905 : RatBall := localContactBall tau1905 center1905
def work1905 : RoundedTauEval :=
  evalTau precision tau1905 contact1905 logTwoBall

theorem center_sq1905 : (center1905.re : ℝ)^2 +
    (center1905.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1905]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1905 : work1905.theta.ok = true ∧
    work1905.jac.invOK = true ∧ acceptsUnitSq work1905.out = true := by decide +kernel

def cell1905 : CellCertificate where
  tauBall := tau1905
  contactCenter := center1905
  contactBall := contact1905
  work := work1905
  center_sq := center_sq1905
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1905.1
  jac_ok := checks1905.2.1
  accepted := checks1905.2.2

def tau1906 : RatBall :=
  ⟨⟨-99/320, 83/320⟩, 3/640⟩
def center1906 : GaussianRat :=
  ⟨-110417413/500000000, 165731261/1000000000⟩
def contact1906 : RatBall := localContactBall tau1906 center1906
def work1906 : RoundedTauEval :=
  evalTau precision tau1906 contact1906 logTwoBall

theorem center_sq1906 : (center1906.re : ℝ)^2 +
    (center1906.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1906]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1906 : work1906.theta.ok = true ∧
    work1906.jac.invOK = true ∧ acceptsUnitSq work1906.out = true := by decide +kernel

def cell1906 : CellCertificate where
  tauBall := tau1906
  contactCenter := center1906
  contactBall := contact1906
  work := work1906
  center_sq := center_sq1906
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1906.1
  jac_ok := checks1906.2.1
  accepted := checks1906.2.2

def tau1907 : RatBall :=
  ⟨⟨-97/320, 83/320⟩, 3/640⟩
def center1907 : GaussianRat :=
  ⟨-108361733/500000000, 83196503/500000000⟩
def contact1907 : RatBall := localContactBall tau1907 center1907
def work1907 : RoundedTauEval :=
  evalTau precision tau1907 contact1907 logTwoBall

theorem center_sq1907 : (center1907.re : ℝ)^2 +
    (center1907.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1907]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1907 : work1907.theta.ok = true ∧
    work1907.jac.invOK = true ∧ acceptsUnitSq work1907.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238


