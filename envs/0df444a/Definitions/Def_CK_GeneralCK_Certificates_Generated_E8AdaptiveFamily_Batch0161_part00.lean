-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0161_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0161_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:15:16.05985+00:00
-- url     : https://prove2.me/theorems/f01a649c-56ff-4c0e-9664-e8dfba1644fb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0161 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1288 : RatBall :=
  ⟨⟨-83/320, -91/320⟩, 3/640⟩
def center1288 : GaussianRat :=
  ⟨-37988073/200000000, -37573667/200000000⟩
def contact1288 : RatBall := localContactBall tau1288 center1288
def work1288 : RoundedTauEval :=
  evalTau precision tau1288 contact1288 logTwoBall

theorem center_sq1288 : (center1288.re : ℝ)^2 +
    (center1288.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1288]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1288 : work1288.theta.ok = true ∧
    work1288.jac.invOK = true ∧ acceptsUnitSq work1288.out = true := by decide +kernel

def cell1288 : CellCertificate where
  tauBall := tau1288
  contactCenter := center1288
  contactBall := contact1288
  work := work1288
  center_sq := center_sq1288
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1288.1
  jac_ok := checks1288.2.1
  accepted := checks1288.2.2

def tau1289 : RatBall :=
  ⟨⟨-81/320, -91/320⟩, 3/640⟩
def center1289 : GaussianRat :=
  ⟨-23204849/125000000, -94265223/500000000⟩
def contact1289 : RatBall := localContactBall tau1289 center1289
def work1289 : RoundedTauEval :=
  evalTau precision tau1289 contact1289 logTwoBall

theorem center_sq1289 : (center1289.re : ℝ)^2 +
    (center1289.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1289]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1289 : work1289.theta.ok = true ∧
    work1289.jac.invOK = true ∧ acceptsUnitSq work1289.out = true := by decide +kernel

def cell1289 : CellCertificate where
  tauBall := tau1289
  contactCenter := center1289
  contactBall := contact1289
  work := work1289
  center_sq := center_sq1289
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1289.1
  jac_ok := checks1289.2.1
  accepted := checks1289.2.2

def tau1290 : RatBall :=
  ⟨⟨-83/320, -89/320⟩, 3/640⟩
def center1290 : GaussianRat :=
  ⟨-189282071/1000000000, -183581561/1000000000⟩
def contact1290 : RatBall := localContactBall tau1290 center1290
def work1290 : RoundedTauEval :=
  evalTau precision tau1290 contact1290 logTwoBall

theorem center_sq1290 : (center1290.re : ℝ)^2 +
    (center1290.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1290]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1290 : work1290.theta.ok = true ∧
    work1290.jac.invOK = true ∧ acceptsUnitSq work1290.out = true := by decide +kernel

def cell1290 : CellCertificate where
  tauBall := tau1290
  contactCenter := center1290
  contactBall := contact1290
  work := work1290
  center_sq := center_sq1290
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1290.1
  jac_ok := checks1290.2.1
  accepted := checks1290.2.2

def tau1291 : RatBall :=
  ⟨⟨-81/320, -89/320⟩, 3/640⟩
def center1291 : GaussianRat :=
  ⟨-92495743/500000000, -184225151/1000000000⟩
def contact1291 : RatBall := localContactBall tau1291 center1291
def work1291 : RoundedTauEval :=
  evalTau precision tau1291 contact1291 logTwoBall

theorem center_sq1291 : (center1291.re : ℝ)^2 +
    (center1291.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1291]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1291 : work1291.theta.ok = true ∧
    work1291.jac.invOK = true ∧ acceptsUnitSq work1291.out = true := by decide +kernel

def cell1291 : CellCertificate where
  tauBall := tau1291
  contactCenter := center1291
  contactBall := contact1291
  work := work1291
  center_sq := center_sq1291
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1291.1
  jac_ok := checks1291.2.1
  accepted := checks1291.2.2

def tau1292 : RatBall :=
  ⟨⟨-19/64, -87/320⟩, 3/640⟩
def center1292 : GaussianRat :=
  ⟨-106965213/500000000, -35068781/200000000⟩
def contact1292 : RatBall := localContactBall tau1292 center1292
def work1292 : RoundedTauEval :=
  evalTau precision tau1292 contact1292 logTwoBall

theorem center_sq1292 : (center1292.re : ℝ)^2 +
    (center1292.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1292]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1292 : work1292.theta.ok = true ∧
    work1292.jac.invOK = true ∧ acceptsUnitSq work1292.out = true := by decide +kernel

def cell1292 : CellCertificate where
  tauBall := tau1292
  contactCenter := center1292
  contactBall := contact1292
  work := work1292
  center_sq := center_sq1292
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1292.1
  jac_ok := checks1292.2.1
  accepted := checks1292.2.2

def tau1293 : RatBall :=
  ⟨⟨-93/320, -87/320⟩, 3/640⟩
def center1293 : GaussianRat :=
  ⟨-1638777/7812500, -17602767/100000000⟩
def contact1293 : RatBall := localContactBall tau1293 center1293

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161


