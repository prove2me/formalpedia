-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0172_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0172_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:43:50.225118+00:00
-- url     : https://prove2.me/theorems/55e2d922-dcf2-452b-9629-d8cab5437620
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0172 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0172_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1380 : RatBall :=
  ⟨⟨-11/64, -111/320⟩, 3/640⟩
def center1380 : GaussianRat :=
  ⟨-133746201/1000000000, -121037589/500000000⟩
def contact1380 : RatBall := localContactBall tau1380 center1380
def work1380 : RoundedTauEval :=
  evalTau precision tau1380 contact1380 logTwoBall

theorem center_sq1380 : (center1380.re : ℝ)^2 +
    (center1380.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1380]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1380 : work1380.theta.ok = true ∧
    work1380.jac.invOK = true ∧ acceptsUnitSq work1380.out = true := by decide +kernel

def cell1380 : CellCertificate where
  tauBall := tau1380
  contactCenter := center1380
  contactBall := contact1380
  work := work1380
  center_sq := center_sq1380
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1380.1
  jac_ok := checks1380.2.1
  accepted := checks1380.2.2

def tau1381 : RatBall :=
  ⟨⟨-53/320, -111/320⟩, 3/640⟩
def center1381 : GaussianRat :=
  ⟨-4032529/31250000, -121353177/500000000⟩
def contact1381 : RatBall := localContactBall tau1381 center1381
def work1381 : RoundedTauEval :=
  evalTau precision tau1381 contact1381 logTwoBall

theorem center_sq1381 : (center1381.re : ℝ)^2 +
    (center1381.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1381]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1381 : work1381.theta.ok = true ∧
    work1381.jac.invOK = true ∧ acceptsUnitSq work1381.out = true := by decide +kernel

def cell1381 : CellCertificate where
  tauBall := tau1381
  contactCenter := center1381
  contactBall := contact1381
  work := work1381
  center_sq := center_sq1381
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1381.1
  jac_ok := checks1381.2.1
  accepted := checks1381.2.2

def tau1382 : RatBall :=
  ⟨⟨-11/64, -109/320⟩, 3/640⟩
def center1382 : GaussianRat :=
  ⟨-133113831/1000000000, -118694053/500000000⟩
def contact1382 : RatBall := localContactBall tau1382 center1382
def work1382 : RoundedTauEval :=
  evalTau precision tau1382 contact1382 logTwoBall

theorem center_sq1382 : (center1382.re : ℝ)^2 +
    (center1382.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1382]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1382 : work1382.theta.ok = true ∧
    work1382.jac.invOK = true ∧ acceptsUnitSq work1382.out = true := by decide +kernel

def cell1382 : CellCertificate where
  tauBall := tau1382
  contactCenter := center1382
  contactBall := contact1382
  work := work1382
  center_sq := center_sq1382
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1382.1
  jac_ok := checks1382.2.1
  accepted := checks1382.2.2

def tau1383 : RatBall :=
  ⟨⟨-53/320, -109/320⟩, 3/640⟩
def center1383 : GaussianRat :=
  ⟨-25685587/200000000, -238002417/1000000000⟩
def contact1383 : RatBall := localContactBall tau1383 center1383
def work1383 : RoundedTauEval :=
  evalTau precision tau1383 contact1383 logTwoBall

theorem center_sq1383 : (center1383.re : ℝ)^2 +
    (center1383.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1383]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1383 : work1383.theta.ok = true ∧
    work1383.jac.invOK = true ∧ acceptsUnitSq work1383.out = true := by decide +kernel

def cell1383 : CellCertificate where
  tauBall := tau1383
  contactCenter := center1383
  contactBall := contact1383
  work := work1383
  center_sq := center_sq1383
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1383.1
  jac_ok := checks1383.2.1
  accepted := checks1383.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172


