-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0039_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0039_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:25:13.577331+00:00
-- url     : https://prove2.me/theorems/f4a065b4-a14b-45e1-afd9-fa68b365fa40
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0039 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0039_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0315 : (center0315.re : ℝ)^2 +
    (center0315.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0315]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0315 : work0315.theta.ok = true ∧
    work0315.jac.invOK = true ∧ acceptsUnitSq work0315.out = true := by decide +kernel

def cell0315 : CellCertificate where
  tauBall := tau0315
  contactCenter := center0315
  contactBall := contact0315
  work := work0315
  center_sq := center_sq0315
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0315.1
  jac_ok := checks0315.2.1
  accepted := checks0315.2.2

def tau0316 : RatBall :=
  ⟨⟨23/80, 9/80⟩, 3/160⟩
def center0316 : GaussianRat :=
  ⟨196096551/1000000000, 71999991/1000000000⟩
def contact0316 : RatBall := localContactBall tau0316 center0316
def work0316 : RoundedTauEval :=
  evalTau precision tau0316 contact0316 logTwoBall

theorem center_sq0316 : (center0316.re : ℝ)^2 +
    (center0316.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0316]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0316 : work0316.theta.ok = true ∧
    work0316.jac.invOK = true ∧ acceptsUnitSq work0316.out = true := by decide +kernel

def cell0316 : CellCertificate where
  tauBall := tau0316
  contactCenter := center0316
  contactBall := contact0316
  work := work0316
  center_sq := center_sq0316
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0316.1
  jac_ok := checks0316.2.1
  accepted := checks0316.2.2

def tau0317 : RatBall :=
  ⟨⟨21/80, 11/80⟩, 3/160⟩
def center0317 : GaussianRat :=
  ⟨90476031/500000000, 89331987/1000000000⟩
def contact0317 : RatBall := localContactBall tau0317 center0317
def work0317 : RoundedTauEval :=
  evalTau precision tau0317 contact0317 logTwoBall

theorem center_sq0317 : (center0317.re : ℝ)^2 +
    (center0317.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0317]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0317 : work0317.theta.ok = true ∧
    work0317.jac.invOK = true ∧ acceptsUnitSq work0317.out = true := by decide +kernel

def cell0317 : CellCertificate where
  tauBall := tau0317
  contactCenter := center0317
  contactBall := contact0317
  work := work0317
  center_sq := center_sq0317
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0317.1
  jac_ok := checks0317.2.1
  accepted := checks0317.2.2

def tau0318 : RatBall :=
  ⟨⟨23/80, 11/80⟩, 3/160⟩
def center0318 : GaussianRat :=
  ⟨19722583/100000000, 88121387/1000000000⟩
def contact0318 : RatBall := localContactBall tau0318 center0318
def work0318 : RoundedTauEval :=
  evalTau precision tau0318 contact0318 logTwoBall

theorem center_sq0318 : (center0318.re : ℝ)^2 +
    (center0318.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0318]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0318 : work0318.theta.ok = true ∧
    work0318.jac.invOK = true ∧ acceptsUnitSq work0318.out = true := by decide +kernel

def cell0318 : CellCertificate where
  tauBall := tau0318
  contactCenter := center0318
  contactBall := contact0318
  work := work0318
  center_sq := center_sq0318
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0318.1
  jac_ok := checks0318.2.1
  accepted := checks0318.2.2

def tau0319 : RatBall :=
  ⟨⟨17/80, 13/80⟩, 3/160⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039


