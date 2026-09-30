-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0238_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0238_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:27:48.00455+00:00
-- url     : https://prove2.me/theorems/02f7163b-9b1a-407b-ab65-720eadffa52f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0238 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0238_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell1907 : CellCertificate where
  tauBall := tau1907
  contactCenter := center1907
  contactBall := contact1907
  work := work1907
  center_sq := center_sq1907
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1907.1
  jac_ok := checks1907.2.1
  accepted := checks1907.2.2

def tau1908 : RatBall :=
  ⟨⟨-97/320, 17/64⟩, 3/640⟩
def center1908 : GaussianRat :=
  ⟨-54347721/250000000, 170518079/1000000000⟩
def contact1908 : RatBall := localContactBall tau1908 center1908
def work1908 : RoundedTauEval :=
  evalTau precision tau1908 contact1908 logTwoBall

theorem center_sq1908 : (center1908.re : ℝ)^2 +
    (center1908.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1908]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1908 : work1908.theta.ok = true ∧
    work1908.jac.invOK = true ∧ acceptsUnitSq work1908.out = true := by decide +kernel

def cell1908 : CellCertificate where
  tauBall := tau1908
  contactCenter := center1908
  contactBall := contact1908
  work := work1908
  center_sq := center_sq1908
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1908.1
  jac_ok := checks1908.2.1
  accepted := checks1908.2.2

def tau1909 : RatBall :=
  ⟨⟨-19/64, 77/320⟩, 3/640⟩
def center1909 : GaussianRat :=
  ⟨-26341087/125000000, 77331419/500000000⟩
def contact1909 : RatBall := localContactBall tau1909 center1909
def work1909 : RoundedTauEval :=
  evalTau precision tau1909 contact1909 logTwoBall

theorem center_sq1909 : (center1909.re : ℝ)^2 +
    (center1909.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1909]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1909 : work1909.theta.ok = true ∧
    work1909.jac.invOK = true ∧ acceptsUnitSq work1909.out = true := by decide +kernel

def cell1909 : CellCertificate where
  tauBall := tau1909
  contactCenter := center1909
  contactBall := contact1909
  work := work1909
  center_sq := center_sq1909
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1909.1
  jac_ok := checks1909.2.1
  accepted := checks1909.2.2

def tau1910 : RatBall :=
  ⟨⟨-93/320, 77/320⟩, 3/640⟩
def center1910 : GaussianRat :=
  ⟨-12912721/62500000, 7762627/50000000⟩
def contact1910 : RatBall := localContactBall tau1910 center1910
def work1910 : RoundedTauEval :=
  evalTau precision tau1910 contact1910 logTwoBall

theorem center_sq1910 : (center1910.re : ℝ)^2 +
    (center1910.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1910]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1910 : work1910.theta.ok = true ∧
    work1910.jac.invOK = true ∧ acceptsUnitSq work1910.out = true := by decide +kernel

def cell1910 : CellCertificate where
  tauBall := tau1910
  contactCenter := center1910
  contactBall := contact1910
  work := work1910
  center_sq := center_sq1910
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1910.1
  jac_ok := checks1910.2.1
  accepted := checks1910.2.2

def tau1911 : RatBall :=
  ⟨⟨-19/64, 79/320⟩, 3/640⟩
def center1911 : GaussianRat :=
  ⟨-211331481/1000000000, 158782791/1000000000⟩
def contact1911 : RatBall := localContactBall tau1911 center1911
def work1911 : RoundedTauEval :=
  evalTau precision tau1911 contact1911 logTwoBall

theorem center_sq1911 : (center1911.re : ℝ)^2 +
    (center1911.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1911]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238


