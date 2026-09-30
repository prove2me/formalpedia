-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0128_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0128_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:59:08.081293+00:00
-- url     : https://prove2.me/theorems/a637714e-4a2c-4a4b-874f-4c7e109af727
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0128 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0128_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1028 : RatBall :=
  ⟨⟨53/160, 23/160⟩, 3/320⟩
def center1028 : GaussianRat :=
  ⟨225467593/1000000000, 89762261/1000000000⟩
def contact1028 : RatBall := localContactBall tau1028 center1028
def work1028 : RoundedTauEval :=
  evalTau precision tau1028 contact1028 logTwoBall

theorem center_sq1028 : (center1028.re : ℝ)^2 +
    (center1028.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1028]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1028 : work1028.theta.ok = true ∧
    work1028.jac.invOK = true ∧ acceptsUnitSq work1028.out = true := by decide +kernel

def cell1028 : CellCertificate where
  tauBall := tau1028
  contactCenter := center1028
  contactBall := contact1028
  work := work1028
  center_sq := center_sq1028
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1028.1
  jac_ok := checks1028.2.1
  accepted := checks1028.2.2

def tau1029 : RatBall :=
  ⟨⟨11/32, 23/160⟩, 3/320⟩
def center1029 : GaussianRat :=
  ⟨58324897/250000000, 11129939/125000000⟩
def contact1029 : RatBall := localContactBall tau1029 center1029
def work1029 : RoundedTauEval :=
  evalTau precision tau1029 contact1029 logTwoBall

theorem center_sq1029 : (center1029.re : ℝ)^2 +
    (center1029.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1029]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1029 : work1029.theta.ok = true ∧
    work1029.jac.invOK = true ∧ acceptsUnitSq work1029.out = true := by decide +kernel

def cell1029 : CellCertificate where
  tauBall := tau1029
  contactCenter := center1029
  contactBall := contact1029
  work := work1029
  center_sq := center_sq1029
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1029.1
  jac_ok := checks1029.2.1
  accepted := checks1029.2.2

def tau1030 : RatBall :=
  ⟨⟨57/160, 17/160⟩, 3/320⟩
def center1030 : GaussianRat :=
  ⟨119567729/500000000, 32582953/500000000⟩
def contact1030 : RatBall := localContactBall tau1030 center1030
def work1030 : RoundedTauEval :=
  evalTau precision tau1030 contact1030 logTwoBall

theorem center_sq1030 : (center1030.re : ℝ)^2 +
    (center1030.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1030]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1030 : work1030.theta.ok = true ∧
    work1030.jac.invOK = true ∧ acceptsUnitSq work1030.out = true := by decide +kernel

def cell1030 : CellCertificate where
  tauBall := tau1030
  contactCenter := center1030
  contactBall := contact1030
  work := work1030
  center_sq := center_sq1030
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1030.1
  jac_ok := checks1030.2.1
  accepted := checks1030.2.2

def tau1031 : RatBall :=
  ⟨⟨59/160, 17/160⟩, 3/320⟩
def center1031 : GaussianRat :=
  ⟨15424847/62500000, 32309019/500000000⟩
def contact1031 : RatBall := localContactBall tau1031 center1031
def work1031 : RoundedTauEval :=
  evalTau precision tau1031 contact1031 logTwoBall

theorem center_sq1031 : (center1031.re : ℝ)^2 +
    (center1031.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1031]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1031 : work1031.theta.ok = true ∧
    work1031.jac.invOK = true ∧ acceptsUnitSq work1031.out = true := by decide +kernel

def cell1031 : CellCertificate where
  tauBall := tau1031
  contactCenter := center1031
  contactBall := contact1031
  work := work1031
  center_sq := center_sq1031
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1031.1
  jac_ok := checks1031.2.1
  accepted := checks1031.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128


