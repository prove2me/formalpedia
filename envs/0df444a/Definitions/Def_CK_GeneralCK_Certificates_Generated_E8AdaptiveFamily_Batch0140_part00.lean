-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0140_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0140_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:16:11.338121+00:00
-- url     : https://prove2.me/theorems/15b82a46-0c73-421a-bf4c-e87fc6aef186
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0140 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1120 : RatBall :=
  ⟨⟨3/160, 53/160⟩, 3/320⟩
def center1120 : GaussianRat :=
  ⟨1832943/125000000, 238869281/1000000000⟩
def contact1120 : RatBall := localContactBall tau1120 center1120
def work1120 : RoundedTauEval :=
  evalTau precision tau1120 contact1120 logTwoBall

theorem center_sq1120 : (center1120.re : ℝ)^2 +
    (center1120.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1120]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1120 : work1120.theta.ok = true ∧
    work1120.jac.invOK = true ∧ acceptsUnitSq work1120.out = true := by decide +kernel

def cell1120 : CellCertificate where
  tauBall := tau1120
  contactCenter := center1120
  contactBall := contact1120
  work := work1120
  center_sq := center_sq1120
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1120.1
  jac_ok := checks1120.2.1
  accepted := checks1120.2.2

def tau1121 : RatBall :=
  ⟨⟨1/160, 11/32⟩, 3/320⟩
def center1121 : GaussianRat :=
  ⟨617179/125000000, 248789139/1000000000⟩
def contact1121 : RatBall := localContactBall tau1121 center1121
def work1121 : RoundedTauEval :=
  evalTau precision tau1121 contact1121 logTwoBall

theorem center_sq1121 : (center1121.re : ℝ)^2 +
    (center1121.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1121]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1121 : work1121.theta.ok = true ∧
    work1121.jac.invOK = true ∧ acceptsUnitSq work1121.out = true := by decide +kernel

def cell1121 : CellCertificate where
  tauBall := tau1121
  contactCenter := center1121
  contactBall := contact1121
  work := work1121
  center_sq := center_sq1121
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1121.1
  jac_ok := checks1121.2.1
  accepted := checks1121.2.2

def tau1122 : RatBall :=
  ⟨⟨3/160, 11/32⟩, 3/320⟩
def center1122 : GaussianRat :=
  ⟨7404737/500000000, 31086129/125000000⟩
def contact1122 : RatBall := localContactBall tau1122 center1122
def work1122 : RoundedTauEval :=
  evalTau precision tau1122 contact1122 logTwoBall

theorem center_sq1122 : (center1122.re : ℝ)^2 +
    (center1122.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1122]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1122 : work1122.theta.ok = true ∧
    work1122.jac.invOK = true ∧ acceptsUnitSq work1122.out = true := by decide +kernel

def cell1122 : CellCertificate where
  tauBall := tau1122
  contactCenter := center1122
  contactBall := contact1122
  work := work1122
  center_sq := center_sq1122
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1122.1
  jac_ok := checks1122.2.1
  accepted := checks1122.2.2

def tau1123 : RatBall :=
  ⟨⟨1/32, 53/160⟩, 3/320⟩
def center1123 : GaussianRat :=
  ⟨2443029/100000000, 119340169/500000000⟩
def contact1123 : RatBall := localContactBall tau1123 center1123
def work1123 : RoundedTauEval :=
  evalTau precision tau1123 contact1123 logTwoBall

theorem center_sq1123 : (center1123.re : ℝ)^2 +
    (center1123.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1123]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1123 : work1123.theta.ok = true ∧
    work1123.jac.invOK = true ∧ acceptsUnitSq work1123.out = true := by decide +kernel

def cell1123 : CellCertificate where
  tauBall := tau1123
  contactCenter := center1123
  contactBall := contact1123
  work := work1123
  center_sq := center_sq1123
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1123.1
  jac_ok := checks1123.2.1
  accepted := checks1123.2.2

def tau1124 : RatBall :=
  ⟨⟨7/160, 53/160⟩, 3/320⟩
def center1124 : GaussianRat :=
  ⟨17091823/500000000, 119198781/500000000⟩
def contact1124 : RatBall := localContactBall tau1124 center1124
def work1124 : RoundedTauEval :=
  evalTau precision tau1124 contact1124 logTwoBall

theorem center_sq1124 : (center1124.re : ℝ)^2 +
    (center1124.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1124]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1124 : work1124.theta.ok = true ∧
    work1124.jac.invOK = true ∧ acceptsUnitSq work1124.out = true := by decide +kernel

def cell1124 : CellCertificate where
  tauBall := tau1124
  contactCenter := center1124
  contactBall := contact1124
  work := work1124
  center_sq := center_sq1124
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1124.1
  jac_ok := checks1124.2.1
  accepted := checks1124.2.2

def tau1125 : RatBall :=
  ⟨⟨1/32, 11/32⟩, 3/320⟩
def center1125 : GaussianRat :=
  ⟨24673061/1000000000, 248489097/1000000000⟩
def contact1125 : RatBall := localContactBall tau1125 center1125
def work1125 : RoundedTauEval :=
  evalTau precision tau1125 contact1125 logTwoBall

theorem center_sq1125 : (center1125.re : ℝ)^2 +
    (center1125.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1125]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1125 : work1125.theta.ok = true ∧
    work1125.jac.invOK = true ∧ acceptsUnitSq work1125.out = true := by decide +kernel

def cell1125 : CellCertificate where
  tauBall := tau1125
  contactCenter := center1125
  contactBall := contact1125
  work := work1125
  center_sq := center_sq1125
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1125.1
  jac_ok := checks1125.2.1
  accepted := checks1125.2.2

def tau1126 : RatBall :=
  ⟨⟨7/160, 11/32⟩, 3/320⟩
def center1126 : GaussianRat :=
  ⟨6904519/200000000, 248189889/1000000000⟩
def contact1126 : RatBall := localContactBall tau1126 center1126
def work1126 : RoundedTauEval :=
  evalTau precision tau1126 contact1126 logTwoBall

theorem center_sq1126 : (center1126.re : ℝ)^2 +
    (center1126.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1126]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140


