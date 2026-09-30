-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0156_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0156_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:48:11.390596+00:00
-- url     : https://prove2.me/theorems/52713ef4-386d-400e-88b4-2008d344cb7d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0156 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0156_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1252 : RatBall :=
  ⟨⟨-103/320, -77/320⟩, 3/640⟩
def center1252 : GaussianRat :=
  ⟨-113522317/500000000, -152229153/1000000000⟩
def contact1252 : RatBall := localContactBall tau1252 center1252
def work1252 : RoundedTauEval :=
  evalTau precision tau1252 contact1252 logTwoBall

theorem center_sq1252 : (center1252.re : ℝ)^2 +
    (center1252.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1252]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1252 : work1252.theta.ok = true ∧
    work1252.jac.invOK = true ∧ acceptsUnitSq work1252.out = true := by decide +kernel

def cell1252 : CellCertificate where
  tauBall := tau1252
  contactCenter := center1252
  contactBall := contact1252
  work := work1252
  center_sq := center_sq1252
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1252.1
  jac_ok := checks1252.2.1
  accepted := checks1252.2.2

def tau1253 : RatBall :=
  ⟨⟨-101/320, -77/320⟩, 3/640⟩
def center1253 : GaussianRat :=
  ⟨-111496867/500000000, -152848327/1000000000⟩
def contact1253 : RatBall := localContactBall tau1253 center1253
def work1253 : RoundedTauEval :=
  evalTau precision tau1253 contact1253 logTwoBall

theorem center_sq1253 : (center1253.re : ℝ)^2 +
    (center1253.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1253]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1253 : work1253.theta.ok = true ∧
    work1253.jac.invOK = true ∧ acceptsUnitSq work1253.out = true := by decide +kernel

def cell1253 : CellCertificate where
  tauBall := tau1253
  contactCenter := center1253
  contactBall := contact1253
  work := work1253
  center_sq := center_sq1253
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1253.1
  jac_ok := checks1253.2.1
  accepted := checks1253.2.2

def tau1254 : RatBall :=
  ⟨⟨-99/320, -79/320⟩, 3/640⟩
def center1254 : GaussianRat :=
  ⟨-109770971/500000000, -78771627/500000000⟩
def contact1254 : RatBall := localContactBall tau1254 center1254
def work1254 : RoundedTauEval :=
  evalTau precision tau1254 contact1254 logTwoBall

theorem center_sq1254 : (center1254.re : ℝ)^2 +
    (center1254.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1254]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1254 : work1254.theta.ok = true ∧
    work1254.jac.invOK = true ∧ acceptsUnitSq work1254.out = true := by decide +kernel

def cell1254 : CellCertificate where
  tauBall := tau1254
  contactCenter := center1254
  contactBall := contact1254
  work := work1254
  center_sq := center_sq1254
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1254.1
  jac_ok := checks1254.2.1
  accepted := checks1254.2.2

def tau1255 : RatBall :=
  ⟨⟨-97/320, -79/320⟩, 3/640⟩
def center1255 : GaussianRat :=
  ⟨-215446071/1000000000, -158166863/1000000000⟩
def contact1255 : RatBall := localContactBall tau1255 center1255
def work1255 : RoundedTauEval :=
  evalTau precision tau1255 contact1255 logTwoBall

theorem center_sq1255 : (center1255.re : ℝ)^2 +
    (center1255.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1255]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1255 : work1255.theta.ok = true ∧
    work1255.jac.invOK = true ∧ acceptsUnitSq work1255.out = true := by decide +kernel

def cell1255 : CellCertificate where
  tauBall := tau1255
  contactCenter := center1255
  contactBall := contact1255
  work := work1255
  center_sq := center_sq1255
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1255.1
  jac_ok := checks1255.2.1
  accepted := checks1255.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156


