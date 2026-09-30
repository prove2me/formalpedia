-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0169_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0169_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:38:59.058613+00:00
-- url     : https://prove2.me/theorems/73c59742-9f3b-4157-ab80-52e9e73b55d3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0169 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1352 : RatBall :=
  ⟨⟨-43/320, -113/320⟩, 3/640⟩
def center1352 : GaussianRat :=
  ⟨-105797499/1000000000, -62590039/250000000⟩
def contact1352 : RatBall := localContactBall tau1352 center1352
def work1352 : RoundedTauEval :=
  evalTau precision tau1352 contact1352 logTwoBall

theorem center_sq1352 : (center1352.re : ℝ)^2 +
    (center1352.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1352]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1352 : work1352.theta.ok = true ∧
    work1352.jac.invOK = true ∧ acceptsUnitSq work1352.out = true := by decide +kernel

def cell1352 : CellCertificate where
  tauBall := tau1352
  contactCenter := center1352
  contactBall := contact1352
  work := work1352
  center_sq := center_sq1352
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1352.1
  jac_ok := checks1352.2.1
  accepted := checks1352.2.2

def tau1353 : RatBall :=
  ⟨⟨-41/320, -113/320⟩, 3/640⟩
def center1353 : GaussianRat :=
  ⟨-100977067/1000000000, -250881183/1000000000⟩
def contact1353 : RatBall := localContactBall tau1353 center1353
def work1353 : RoundedTauEval :=
  evalTau precision tau1353 contact1353 logTwoBall

theorem center_sq1353 : (center1353.re : ℝ)^2 +
    (center1353.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1353]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1353 : work1353.theta.ok = true ∧
    work1353.jac.invOK = true ∧ acceptsUnitSq work1353.out = true := by decide +kernel

def cell1353 : CellCertificate where
  tauBall := tau1353
  contactCenter := center1353
  contactBall := contact1353
  work := work1353
  center_sq := center_sq1353
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1353.1
  jac_ok := checks1353.2.1
  accepted := checks1353.2.2

def tau1354 : RatBall :=
  ⟨⟨-39/320, -117/320⟩, 3/640⟩
def center1354 : GaussianRat :=
  ⟨-97144261/1000000000, -261108469/1000000000⟩
def contact1354 : RatBall := localContactBall tau1354 center1354
def work1354 : RoundedTauEval :=
  evalTau precision tau1354 contact1354 logTwoBall

theorem center_sq1354 : (center1354.re : ℝ)^2 +
    (center1354.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1354]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1354 : work1354.theta.ok = true ∧
    work1354.jac.invOK = true ∧ acceptsUnitSq work1354.out = true := by decide +kernel

def cell1354 : CellCertificate where
  tauBall := tau1354
  contactCenter := center1354
  contactBall := contact1354
  work := work1354
  center_sq := center_sq1354
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1354.1
  jac_ok := checks1354.2.1
  accepted := checks1354.2.2

def tau1355 : RatBall :=
  ⟨⟨-37/320, -117/320⟩, 3/640⟩
def center1355 : GaussianRat :=
  ⟨-46124689/500000000, -261610997/1000000000⟩
def contact1355 : RatBall := localContactBall tau1355 center1355
def work1355 : RoundedTauEval :=
  evalTau precision tau1355 contact1355 logTwoBall

theorem center_sq1355 : (center1355.re : ℝ)^2 +
    (center1355.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1355]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1355 : work1355.theta.ok = true ∧
    work1355.jac.invOK = true ∧ acceptsUnitSq work1355.out = true := by decide +kernel

def cell1355 : CellCertificate where
  tauBall := tau1355
  contactCenter := center1355
  contactBall := contact1355
  work := work1355
  center_sq := center_sq1355
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1355.1
  jac_ok := checks1355.2.1
  accepted := checks1355.2.2

def tau1356 : RatBall :=
  ⟨⟨-7/64, -117/320⟩, 3/640⟩
def center1356 : GaussianRat :=
  ⟨-43670547/500000000, -65522293/250000000⟩
def contact1356 : RatBall := localContactBall tau1356 center1356
def work1356 : RoundedTauEval :=
  evalTau precision tau1356 contact1356 logTwoBall

theorem center_sq1356 : (center1356.re : ℝ)^2 +
    (center1356.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1356]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1356 : work1356.theta.ok = true ∧
    work1356.jac.invOK = true ∧ acceptsUnitSq work1356.out = true := by decide +kernel

def cell1356 : CellCertificate where
  tauBall := tau1356
  contactCenter := center1356
  contactBall := contact1356
  work := work1356
  center_sq := center_sq1356
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1356.1
  jac_ok := checks1356.2.1
  accepted := checks1356.2.2

def tau1357 : RatBall :=
  ⟨⟨-33/320, -117/320⟩, 3/640⟩
def center1357 : GaussianRat :=
  ⟨-1648401/20000000, -65635667/250000000⟩
def contact1357 : RatBall := localContactBall tau1357 center1357
def work1357 : RoundedTauEval :=
  evalTau precision tau1357 contact1357 logTwoBall

theorem center_sq1357 : (center1357.re : ℝ)^2 +
    (center1357.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1357]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1357 : work1357.theta.ok = true ∧
    work1357.jac.invOK = true ∧ acceptsUnitSq work1357.out = true := by decide +kernel

def cell1357 : CellCertificate where
  tauBall := tau1357
  contactCenter := center1357
  contactBall := contact1357
  work := work1357
  center_sq := center_sq1357
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1357.1
  jac_ok := checks1357.2.1
  accepted := checks1357.2.2

def tau1358 : RatBall :=
  ⟨⟨-39/320, -23/64⟩, 3/640⟩
def center1358 : GaussianRat :=
  ⟨-773093/8000000, -128116201/500000000⟩
def contact1358 : RatBall := localContactBall tau1358 center1358
def work1358 : RoundedTauEval :=
  evalTau precision tau1358 contact1358 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169


