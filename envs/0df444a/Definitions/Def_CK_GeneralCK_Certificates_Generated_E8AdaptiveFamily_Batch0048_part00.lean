-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0048_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0048_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:26:21.616415+00:00
-- url     : https://prove2.me/theorems/ab131e52-34b4-4887-bf26-e9f002f8ed28
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0048 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0384 : RatBall :=
  ⟨⟨-33/160, -37/160⟩, 3/320⟩
def center0384 : GaussianRat :=
  ⟨-148574359/1000000000, -31163137/200000000⟩
def contact0384 : RatBall := localContactBall tau0384 center0384
def work0384 : RoundedTauEval :=
  evalTau precision tau0384 contact0384 logTwoBall

theorem center_sq0384 : (center0384.re : ℝ)^2 +
    (center0384.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0384]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0384 : work0384.theta.ok = true ∧
    work0384.jac.invOK = true ∧ acceptsUnitSq work0384.out = true := by decide +kernel

def cell0384 : CellCertificate where
  tauBall := tau0384
  contactCenter := center0384
  contactBall := contact0384
  work := work0384
  center_sq := center_sq0384
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0384.1
  jac_ok := checks0384.2.1
  accepted := checks0384.2.2

def tau0385 : RatBall :=
  ⟨⟨-39/160, -7/32⟩, 3/320⟩
def center0385 : GaussianRat :=
  ⟨-173384937/1000000000, -144541281/1000000000⟩
def contact0385 : RatBall := localContactBall tau0385 center0385
def work0385 : RoundedTauEval :=
  evalTau precision tau0385 contact0385 logTwoBall

theorem center_sq0385 : (center0385.re : ℝ)^2 +
    (center0385.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0385]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0385 : work0385.theta.ok = true ∧
    work0385.jac.invOK = true ∧ acceptsUnitSq work0385.out = true := by decide +kernel

def cell0385 : CellCertificate where
  tauBall := tau0385
  contactCenter := center0385
  contactBall := contact0385
  work := work0385
  center_sq := center_sq0385
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0385.1
  jac_ok := checks0385.2.1
  accepted := checks0385.2.2

def tau0386 : RatBall :=
  ⟨⟨-37/160, -7/32⟩, 3/320⟩
def center0386 : GaussianRat :=
  ⟨-164892819/1000000000, -29090197/200000000⟩
def contact0386 : RatBall := localContactBall tau0386 center0386
def work0386 : RoundedTauEval :=
  evalTau precision tau0386 contact0386 logTwoBall

theorem center_sq0386 : (center0386.re : ℝ)^2 +
    (center0386.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0386]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0386 : work0386.theta.ok = true ∧
    work0386.jac.invOK = true ∧ acceptsUnitSq work0386.out = true := by decide +kernel

def cell0386 : CellCertificate where
  tauBall := tau0386
  contactCenter := center0386
  contactBall := contact0386
  work := work0386
  center_sq := center_sq0386
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0386.1
  jac_ok := checks0386.2.1
  accepted := checks0386.2.2

def tau0387 : RatBall :=
  ⟨⟨-39/160, -33/160⟩, 3/320⟩
def center0387 : GaussianRat :=
  ⟨-172488051/1000000000, -136096987/1000000000⟩
def contact0387 : RatBall := localContactBall tau0387 center0387
def work0387 : RoundedTauEval :=
  evalTau precision tau0387 contact0387 logTwoBall

theorem center_sq0387 : (center0387.re : ℝ)^2 +
    (center0387.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0387]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0387 : work0387.theta.ok = true ∧
    work0387.jac.invOK = true ∧ acceptsUnitSq work0387.out = true := by decide +kernel

def cell0387 : CellCertificate where
  tauBall := tau0387
  contactCenter := center0387
  contactBall := contact0387
  work := work0387
  center_sq := center_sq0387
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0387.1
  jac_ok := checks0387.2.1
  accepted := checks0387.2.2

def tau0388 : RatBall :=
  ⟨⟨-37/160, -33/160⟩, 3/320⟩
def center0388 : GaussianRat :=
  ⟨-164030831/1000000000, -3423667/25000000⟩
def contact0388 : RatBall := localContactBall tau0388 center0388
def work0388 : RoundedTauEval :=
  evalTau precision tau0388 contact0388 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048


