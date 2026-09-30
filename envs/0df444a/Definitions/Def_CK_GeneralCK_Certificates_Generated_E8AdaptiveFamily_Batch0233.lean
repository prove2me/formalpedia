-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0233
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0233
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:41:21.537516+00:00
-- url     : https://prove2.me/theorems/7e2f74d5-32b1-4d4f-ad4b-6c2e7a8c7e64
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0233.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0233_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1869 : RoundedTauEval :=
  evalTau precision tau1869 contact1869 logTwoBall

theorem center_sq1869 : (center1869.re : ℝ)^2 +
    (center1869.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1869]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1869 : work1869.theta.ok = true ∧
    work1869.jac.invOK = true ∧ acceptsUnitSq work1869.out = true := by decide +kernel

def cell1869 : CellCertificate where
  tauBall := tau1869
  contactCenter := center1869
  contactBall := contact1869
  work := work1869
  center_sq := center_sq1869
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1869.1
  jac_ok := checks1869.2.1
  accepted := checks1869.2.2

def tau1870 : RatBall :=
  ⟨⟨103/320, -73/320⟩, 3/640⟩
def center1870 : GaussianRat :=
  ⟨5645929/25000000, -9009977/62500000⟩
def contact1870 : RatBall := localContactBall tau1870 center1870
def work1870 : RoundedTauEval :=
  evalTau precision tau1870 contact1870 logTwoBall

theorem center_sq1870 : (center1870.re : ℝ)^2 +
    (center1870.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1870]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1870 : work1870.theta.ok = true ∧
    work1870.jac.invOK = true ∧ acceptsUnitSq work1870.out = true := by decide +kernel

def cell1870 : CellCertificate where
  tauBall := tau1870
  contactCenter := center1870
  contactBall := contact1870
  work := work1870
  center_sq := center_sq1870
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1870.1
  jac_ok := checks1870.2.1
  accepted := checks1870.2.2

def tau1871 : RatBall :=
  ⟨⟨21/64, -15/64⟩, 3/640⟩
def center1871 : GaussianRat :=
  ⟨14403551/62500000, -14758413/100000000⟩
def contact1871 : RatBall := localContactBall tau1871 center1871
def work1871 : RoundedTauEval :=
  evalTau precision tau1871 contact1871 logTwoBall

theorem center_sq1871 : (center1871.re : ℝ)^2 +
    (center1871.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1871]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1871 : work1871.theta.ok = true ∧
    work1871.jac.invOK = true ∧ acceptsUnitSq work1871.out = true := by decide +kernel

def cell1871 : CellCertificate where
  tauBall := tau1871
  contactCenter := center1871
  contactBall := contact1871
  work := work1871
  center_sq := center_sq1871
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1871.1
  jac_ok := checks1871.2.1
  accepted := checks1871.2.2

def cells : List CellCertificate := [cell1864, cell1865, cell1866, cell1867, cell1868, cell1869, cell1870, cell1871]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233


