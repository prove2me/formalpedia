-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0150_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0150_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:55:51.337301+00:00
-- url     : https://prove2.me/theorems/eff74e2b-cf49-4048-a9ad-7b3f9ba15881
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0150 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1200 : RatBall :=
  ⟨⟨-17/64, -97/320⟩, 3/640⟩
def center1200 : GaussianRat :=
  ⟨-49086427/250000000, -200064207/1000000000⟩
def contact1200 : RatBall := localContactBall tau1200 center1200
def work1200 : RoundedTauEval :=
  evalTau precision tau1200 contact1200 logTwoBall

theorem center_sq1200 : (center1200.re : ℝ)^2 +
    (center1200.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1200]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1200 : work1200.theta.ok = true ∧
    work1200.jac.invOK = true ∧ acceptsUnitSq work1200.out = true := by decide +kernel

def cell1200 : CellCertificate where
  tauBall := tau1200
  contactCenter := center1200
  contactBall := contact1200
  work := work1200
  center_sq := center_sq1200
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1200.1
  jac_ok := checks1200.2.1
  accepted := checks1200.2.2

def tau1201 : RatBall :=
  ⟨⟨-83/320, -99/320⟩, 3/640⟩
def center1201 : GaussianRat :=
  ⟨-19276477/100000000, -205127733/1000000000⟩
def contact1201 : RatBall := localContactBall tau1201 center1201
def work1201 : RoundedTauEval :=
  evalTau precision tau1201 contact1201 logTwoBall

theorem center_sq1201 : (center1201.re : ℝ)^2 +
    (center1201.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1201]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1201 : work1201.theta.ok = true ∧
    work1201.jac.invOK = true ∧ acceptsUnitSq work1201.out = true := by decide +kernel

def cell1201 : CellCertificate where
  tauBall := tau1201
  contactCenter := center1201
  contactBall := contact1201
  work := work1201
  center_sq := center_sq1201
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1201.1
  jac_ok := checks1201.2.1
  accepted := checks1201.2.2

def tau1202 : RatBall :=
  ⟨⟨-81/320, -99/320⟩, 3/640⟩
def center1202 : GaussianRat :=
  ⟨-47104143/250000000, -25733387/125000000⟩
def contact1202 : RatBall := localContactBall tau1202 center1202
def work1202 : RoundedTauEval :=
  evalTau precision tau1202 contact1202 logTwoBall

theorem center_sq1202 : (center1202.re : ℝ)^2 +
    (center1202.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1202]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1202 : work1202.theta.ok = true ∧
    work1202.jac.invOK = true ∧ acceptsUnitSq work1202.out = true := by decide +kernel

def cell1202 : CellCertificate where
  tauBall := tau1202
  contactCenter := center1202
  contactBall := contact1202
  work := work1202
  center_sq := center_sq1202
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1202.1
  jac_ok := checks1202.2.1
  accepted := checks1202.2.2

def tau1203 : RatBall :=
  ⟨⟨-83/320, -97/320⟩, 3/640⟩
def center1203 : GaussianRat :=
  ⟨-9601467/50000000, -100397757/500000000⟩
def contact1203 : RatBall := localContactBall tau1203 center1203
def work1203 : RoundedTauEval :=
  evalTau precision tau1203 contact1203 logTwoBall

theorem center_sq1203 : (center1203.re : ℝ)^2 +
    (center1203.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1203]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1203 : work1203.theta.ok = true ∧
    work1203.jac.invOK = true ∧ acceptsUnitSq work1203.out = true := by decide +kernel

def cell1203 : CellCertificate where
  tauBall := tau1203
  contactCenter := center1203
  contactBall := contact1203
  work := work1203
  center_sq := center_sq1203
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1203.1
  jac_ok := checks1203.2.1
  accepted := checks1203.2.2

def tau1204 : RatBall :=
  ⟨⟨-81/320, -97/320⟩, 3/640⟩
def center1204 : GaussianRat :=
  ⟨-469233/2500000, -201515067/1000000000⟩
def contact1204 : RatBall := localContactBall tau1204 center1204
def work1204 : RoundedTauEval :=
  evalTau precision tau1204 contact1204 logTwoBall

theorem center_sq1204 : (center1204.re : ℝ)^2 +
    (center1204.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1204]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1204 : work1204.theta.ok = true ∧
    work1204.jac.invOK = true ∧ acceptsUnitSq work1204.out = true := by decide +kernel

def cell1204 : CellCertificate where
  tauBall := tau1204
  contactCenter := center1204
  contactBall := contact1204
  work := work1204
  center_sq := center_sq1204
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1204.1
  jac_ok := checks1204.2.1
  accepted := checks1204.2.2

def tau1205 : RatBall :=
  ⟨⟨-73/320, -21/64⟩, 3/640⟩
def center1205 : GaussianRat :=
  ⟨-172956611/1000000000, -222066431/1000000000⟩
def contact1205 : RatBall := localContactBall tau1205 center1205
def work1205 : RoundedTauEval :=
  evalTau precision tau1205 contact1205 logTwoBall

theorem center_sq1205 : (center1205.re : ℝ)^2 +
    (center1205.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1205]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1205 : work1205.theta.ok = true ∧
    work1205.jac.invOK = true ∧ acceptsUnitSq work1205.out = true := by decide +kernel

def cell1205 : CellCertificate where
  tauBall := tau1205
  contactCenter := center1205
  contactBall := contact1205
  work := work1205
  center_sq := center_sq1205
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1205.1
  jac_ok := checks1205.2.1
  accepted := checks1205.2.2

def tau1206 : RatBall :=
  ⟨⟨-69/320, -107/320⟩, 3/640⟩
def center1206 : GaussianRat :=
  ⟨-20584937/125000000, -228038057/1000000000⟩
def contact1206 : RatBall := localContactBall tau1206 center1206

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150


