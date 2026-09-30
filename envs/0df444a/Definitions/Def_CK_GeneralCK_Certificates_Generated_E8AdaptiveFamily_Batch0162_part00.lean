-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0162_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0162_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:18:51.442448+00:00
-- url     : https://prove2.me/theorems/8cfa4b1d-a091-418f-9f4f-e00ad3e96cb5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0162 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1296 : RatBall :=
  ⟨⟨-91/320, -87/320⟩, 3/640⟩
def center1296 : GaussianRat :=
  ⟨-102788551/500000000, -176702417/1000000000⟩
def contact1296 : RatBall := localContactBall tau1296 center1296
def work1296 : RoundedTauEval :=
  evalTau precision tau1296 contact1296 logTwoBall

theorem center_sq1296 : (center1296.re : ℝ)^2 +
    (center1296.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1296]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1296 : work1296.theta.ok = true ∧
    work1296.jac.invOK = true ∧ acceptsUnitSq work1296.out = true := by decide +kernel

def cell1296 : CellCertificate where
  tauBall := tau1296
  contactCenter := center1296
  contactBall := contact1296
  work := work1296
  center_sq := center_sq1296
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1296.1
  jac_ok := checks1296.2.1
  accepted := checks1296.2.2

def tau1297 : RatBall :=
  ⟨⟨-89/320, -87/320⟩, 3/640⟩
def center1297 : GaussianRat :=
  ⟨-201371579/1000000000, -177367859/1000000000⟩
def contact1297 : RatBall := localContactBall tau1297 center1297
def work1297 : RoundedTauEval :=
  evalTau precision tau1297 contact1297 logTwoBall

theorem center_sq1297 : (center1297.re : ℝ)^2 +
    (center1297.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1297]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1297 : work1297.theta.ok = true ∧
    work1297.jac.invOK = true ∧ acceptsUnitSq work1297.out = true := by decide +kernel

def cell1297 : CellCertificate where
  tauBall := tau1297
  contactCenter := center1297
  contactBall := contact1297
  work := work1297
  center_sq := center_sq1297
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1297.1
  jac_ok := checks1297.2.1
  accepted := checks1297.2.2

def tau1298 : RatBall :=
  ⟨⟨-91/320, -17/64⟩, 3/640⟩
def center1298 : GaussianRat :=
  ⟨-102458249/500000000, -172511057/1000000000⟩
def contact1298 : RatBall := localContactBall tau1298 center1298
def work1298 : RoundedTauEval :=
  evalTau precision tau1298 contact1298 logTwoBall

theorem center_sq1298 : (center1298.re : ℝ)^2 +
    (center1298.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1298]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1298 : work1298.theta.ok = true ∧
    work1298.jac.invOK = true ∧ acceptsUnitSq work1298.out = true := by decide +kernel

def cell1298 : CellCertificate where
  tauBall := tau1298
  contactCenter := center1298
  contactBall := contact1298
  work := work1298
  center_sq := center_sq1298
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1298.1
  jac_ok := checks1298.2.1
  accepted := checks1298.2.2

def tau1299 : RatBall :=
  ⟨⟨-89/320, -17/64⟩, 3/640⟩
def center1299 : GaussianRat :=
  ⟨-20072031/100000000, -86578791/500000000⟩
def contact1299 : RatBall := localContactBall tau1299 center1299
def work1299 : RoundedTauEval :=
  evalTau precision tau1299 contact1299 logTwoBall

theorem center_sq1299 : (center1299.re : ℝ)^2 +
    (center1299.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1299]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1299 : work1299.theta.ok = true ∧
    work1299.jac.invOK = true ∧ acceptsUnitSq work1299.out = true := by decide +kernel

def cell1299 : CellCertificate where
  tauBall := tau1299
  contactCenter := center1299
  contactBall := contact1299
  work := work1299
  center_sq := center_sq1299
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1299.1
  jac_ok := checks1299.2.1
  accepted := checks1299.2.2

def tau1300 : RatBall :=
  ⟨⟨-19/64, -83/320⟩, 3/640⟩
def center1300 : GaussianRat :=
  ⟨-212592873/1000000000, -33409337/200000000⟩
def contact1300 : RatBall := localContactBall tau1300 center1300
def work1300 : RoundedTauEval :=
  evalTau precision tau1300 contact1300 logTwoBall

theorem center_sq1300 : (center1300.re : ℝ)^2 +
    (center1300.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1300]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1300 : work1300.theta.ok = true ∧
    work1300.jac.invOK = true ∧ acceptsUnitSq work1300.out = true := by decide +kernel

def cell1300 : CellCertificate where
  tauBall := tau1300
  contactCenter := center1300
  contactBall := contact1300
  work := work1300
  center_sq := center_sq1300
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1300.1
  jac_ok := checks1300.2.1
  accepted := checks1300.2.2

def tau1301 : RatBall :=
  ⟨⟨-93/320, -83/320⟩, 3/640⟩
def center1301 : GaussianRat :=
  ⟨-52110811/250000000, -167692033/1000000000⟩
def contact1301 : RatBall := localContactBall tau1301 center1301

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162


