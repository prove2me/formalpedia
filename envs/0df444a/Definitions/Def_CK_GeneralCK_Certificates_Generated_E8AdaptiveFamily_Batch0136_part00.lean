-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0136_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0136_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:55:09.830981+00:00
-- url     : https://prove2.me/theorems/703dc769-6742-44ea-b72a-4adf0cdbb097
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0136 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1088 : RatBall :=
  ⟨⟨19/160, 9/32⟩, 3/320⟩
def center1088 : GaussianRat :=
  ⟨22260513/250000000, 49311287/250000000⟩
def contact1088 : RatBall := localContactBall tau1088 center1088
def work1088 : RoundedTauEval :=
  evalTau precision tau1088 contact1088 logTwoBall

theorem center_sq1088 : (center1088.re : ℝ)^2 +
    (center1088.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1088]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1088 : work1088.theta.ok = true ∧
    work1088.jac.invOK = true ∧ acceptsUnitSq work1088.out = true := by decide +kernel

def cell1088 : CellCertificate where
  tauBall := tau1088
  contactCenter := center1088
  contactBall := contact1088
  work := work1088
  center_sq := center_sq1088
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1088.1
  jac_ok := checks1088.2.1
  accepted := checks1088.2.2

def tau1089 : RatBall :=
  ⟨⟨17/160, 47/160⟩, 3/320⟩
def center1089 : GaussianRat :=
  ⟨20104647/250000000, 10360657/50000000⟩
def contact1089 : RatBall := localContactBall tau1089 center1089
def work1089 : RoundedTauEval :=
  evalTau precision tau1089 contact1089 logTwoBall

theorem center_sq1089 : (center1089.re : ℝ)^2 +
    (center1089.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1089]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1089 : work1089.theta.ok = true ∧
    work1089.jac.invOK = true ∧ acceptsUnitSq work1089.out = true := by decide +kernel

def cell1089 : CellCertificate where
  tauBall := tau1089
  contactCenter := center1089
  contactBall := contact1089
  work := work1089
  center_sq := center_sq1089
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1089.1
  jac_ok := checks1089.2.1
  accepted := checks1089.2.2

def tau1090 : RatBall :=
  ⟨⟨19/160, 47/160⟩, 3/320⟩
def center1090 : GaussianRat :=
  ⟨89749431/1000000000, 206520639/1000000000⟩
def contact1090 : RatBall := localContactBall tau1090 center1090
def work1090 : RoundedTauEval :=
  evalTau precision tau1090 contact1090 logTwoBall

theorem center_sq1090 : (center1090.re : ℝ)^2 +
    (center1090.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1090]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1090 : work1090.theta.ok = true ∧
    work1090.jac.invOK = true ∧ acceptsUnitSq work1090.out = true := by decide +kernel

def cell1090 : CellCertificate where
  tauBall := tau1090
  contactCenter := center1090
  contactBall := contact1090
  work := work1090
  center_sq := center_sq1090
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1090.1
  jac_ok := checks1090.2.1
  accepted := checks1090.2.2

def tau1091 : RatBall :=
  ⟨⟨21/160, 9/32⟩, 3/320⟩
def center1091 : GaussianRat :=
  ⟨2456559/25000000, 19652513/100000000⟩
def contact1091 : RatBall := localContactBall tau1091 center1091
def work1091 : RoundedTauEval :=
  evalTau precision tau1091 contact1091 logTwoBall

theorem center_sq1091 : (center1091.re : ℝ)^2 +
    (center1091.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1091]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1091 : work1091.theta.ok = true ∧
    work1091.jac.invOK = true ∧ acceptsUnitSq work1091.out = true := by decide +kernel

def cell1091 : CellCertificate where
  tauBall := tau1091
  contactCenter := center1091
  contactBall := contact1091
  work := work1091
  center_sq := center_sq1091
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1091.1
  jac_ok := checks1091.2.1
  accepted := checks1091.2.2

def tau1092 : RatBall :=
  ⟨⟨23/160, 9/32⟩, 3/320⟩
def center1092 : GaussianRat :=
  ⟨107438161/1000000000, 195739697/1000000000⟩
def contact1092 : RatBall := localContactBall tau1092 center1092
def work1092 : RoundedTauEval :=
  evalTau precision tau1092 contact1092 logTwoBall

theorem center_sq1092 : (center1092.re : ℝ)^2 +
    (center1092.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1092]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1092 : work1092.theta.ok = true ∧
    work1092.jac.invOK = true ∧ acceptsUnitSq work1092.out = true := by decide +kernel

def cell1092 : CellCertificate where
  tauBall := tau1092
  contactCenter := center1092
  contactBall := contact1092
  work := work1092
  center_sq := center_sq1092
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1092.1
  jac_ok := checks1092.2.1
  accepted := checks1092.2.2

def tau1093 : RatBall :=
  ⟨⟨21/160, 47/160⟩, 3/320⟩
def center1093 : GaussianRat :=
  ⟨618987/6250000, 102878573/500000000⟩
def contact1093 : RatBall := localContactBall tau1093 center1093
def work1093 : RoundedTauEval :=
  evalTau precision tau1093 contact1093 logTwoBall

theorem center_sq1093 : (center1093.re : ℝ)^2 +
    (center1093.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1093]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1093 : work1093.theta.ok = true ∧
    work1093.jac.invOK = true ∧ acceptsUnitSq work1093.out = true := by decide +kernel

def cell1093 : CellCertificate where
  tauBall := tau1093
  contactCenter := center1093
  contactBall := contact1093
  work := work1093
  center_sq := center_sq1093
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1093.1
  jac_ok := checks1093.2.1
  accepted := checks1093.2.2

def tau1094 : RatBall :=
  ⟨⟨23/160, 47/160⟩, 3/320⟩
def center1094 : GaussianRat :=
  ⟨108280123/1000000000, 204924443/1000000000⟩
def contact1094 : RatBall := localContactBall tau1094 center1094
def work1094 : RoundedTauEval :=
  evalTau precision tau1094 contact1094 logTwoBall

theorem center_sq1094 : (center1094.re : ℝ)^2 +
    (center1094.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1094]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136


