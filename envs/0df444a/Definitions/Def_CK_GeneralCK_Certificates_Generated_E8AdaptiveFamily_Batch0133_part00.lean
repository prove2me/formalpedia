-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0133_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0133_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:35:50.329749+00:00
-- url     : https://prove2.me/theorems/2a717a64-807a-4540-b843-289e7e2c4b68
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0133 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1064 : RatBall :=
  ⟨⟨11/160, 9/32⟩, 3/320⟩
def center1064 : GaussianRat :=
  ⟨25896777/500000000, 199440199/1000000000⟩
def contact1064 : RatBall := localContactBall tau1064 center1064
def work1064 : RoundedTauEval :=
  evalTau precision tau1064 contact1064 logTwoBall

theorem center_sq1064 : (center1064.re : ℝ)^2 +
    (center1064.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1064]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1064 : work1064.theta.ok = true ∧
    work1064.jac.invOK = true ∧ acceptsUnitSq work1064.out = true := by decide +kernel

def cell1064 : CellCertificate where
  tauBall := tau1064
  contactCenter := center1064
  contactBall := contact1064
  work := work1064
  center_sq := center_sq1064
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1064.1
  jac_ok := checks1064.2.1
  accepted := checks1064.2.2

def tau1065 : RatBall :=
  ⟨⟨9/160, 47/160⟩, 3/320⟩
def center1065 : GaussianRat :=
  ⟨42754839/1000000000, 41848559/200000000⟩
def contact1065 : RatBall := localContactBall tau1065 center1065
def work1065 : RoundedTauEval :=
  evalTau precision tau1065 contact1065 logTwoBall

theorem center_sq1065 : (center1065.re : ℝ)^2 +
    (center1065.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1065]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1065 : work1065.theta.ok = true ∧
    work1065.jac.invOK = true ∧ acceptsUnitSq work1065.out = true := by decide +kernel

def cell1065 : CellCertificate where
  tauBall := tau1065
  contactCenter := center1065
  contactBall := contact1065
  work := work1065
  center_sq := center_sq1065
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1065.1
  jac_ok := checks1065.2.1
  accepted := checks1065.2.2

def tau1066 : RatBall :=
  ⟨⟨11/160, 47/160⟩, 3/320⟩
def center1066 : GaussianRat :=
  ⟨13053307/250000000, 208849073/1000000000⟩
def contact1066 : RatBall := localContactBall tau1066 center1066
def work1066 : RoundedTauEval :=
  evalTau precision tau1066 contact1066 logTwoBall

theorem center_sq1066 : (center1066.re : ℝ)^2 +
    (center1066.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1066]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1066 : work1066.theta.ok = true ∧
    work1066.jac.invOK = true ∧ acceptsUnitSq work1066.out = true := by decide +kernel

def cell1066 : CellCertificate where
  tauBall := tau1066
  contactCenter := center1066
  contactBall := contact1066
  work := work1066
  center_sq := center_sq1066
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1066.1
  jac_ok := checks1066.2.1
  accepted := checks1066.2.2

def tau1067 : RatBall :=
  ⟨⟨13/160, 9/32⟩, 3/320⟩
def center1067 : GaussianRat :=
  ⟨30576347/500000000, 99498463/500000000⟩
def contact1067 : RatBall := localContactBall tau1067 center1067
def work1067 : RoundedTauEval :=
  evalTau precision tau1067 contact1067 logTwoBall

theorem center_sq1067 : (center1067.re : ℝ)^2 +
    (center1067.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1067]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1067 : work1067.theta.ok = true ∧
    work1067.jac.invOK = true ∧ acceptsUnitSq work1067.out = true := by decide +kernel

def cell1067 : CellCertificate where
  tauBall := tau1067
  contactCenter := center1067
  contactBall := contact1067
  work := work1067
  center_sq := center_sq1067
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1067.1
  jac_ok := checks1067.2.1
  accepted := checks1067.2.2

def tau1068 : RatBall :=
  ⟨⟨3/32, 9/32⟩, 3/320⟩
def center1068 : GaussianRat :=
  ⟨17620809/250000000, 24810311/125000000⟩
def contact1068 : RatBall := localContactBall tau1068 center1068
def work1068 : RoundedTauEval :=
  evalTau precision tau1068 contact1068 logTwoBall

theorem center_sq1068 : (center1068.re : ℝ)^2 +
    (center1068.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1068]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1068 : work1068.theta.ok = true ∧
    work1068.jac.invOK = true ∧ acceptsUnitSq work1068.out = true := by decide +kernel

def cell1068 : CellCertificate where
  tauBall := tau1068
  contactCenter := center1068
  contactBall := contact1068
  work := work1068
  center_sq := center_sq1068
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1068.1
  jac_ok := checks1068.2.1
  accepted := checks1068.2.2

def tau1069 : RatBall :=
  ⟨⟨13/160, 47/160⟩, 3/320⟩
def center1069 : GaussianRat :=
  ⟨61646237/1000000000, 5209469/25000000⟩
def contact1069 : RatBall := localContactBall tau1069 center1069
def work1069 : RoundedTauEval :=
  evalTau precision tau1069 contact1069 logTwoBall

theorem center_sq1069 : (center1069.re : ℝ)^2 +
    (center1069.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1069]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1069 : work1069.theta.ok = true ∧
    work1069.jac.invOK = true ∧ acceptsUnitSq work1069.out = true := by decide +kernel

def cell1069 : CellCertificate where
  tauBall := tau1069
  contactCenter := center1069
  contactBall := contact1069
  work := work1069
  center_sq := center_sq1069
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1069.1
  jac_ok := checks1069.2.1
  accepted := checks1069.2.2

def tau1070 : RatBall :=
  ⟨⟨3/32, 47/160⟩, 3/320⟩
def center1070 : GaussianRat :=
  ⟨71049459/1000000000, 207833009/1000000000⟩
def contact1070 : RatBall := localContactBall tau1070 center1070
def work1070 : RoundedTauEval :=
  evalTau precision tau1070 contact1070 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133


