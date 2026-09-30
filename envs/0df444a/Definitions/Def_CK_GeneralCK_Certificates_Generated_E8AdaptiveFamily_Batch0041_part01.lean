-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0041_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0041_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:49:06.697092+00:00
-- url     : https://prove2.me/theorems/40d09089-c52f-4dc2-9bbe-e76f8638e945
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0041 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0041 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0041 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0041 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0041 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0041_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0041

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work0331 : RoundedTauEval :=
  evalTau precision tau0331 contact0331 logTwoBall

theorem center_sq0331 : (center0331.re : ℝ)^2 +
    (center0331.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0331]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0331 : work0331.theta.ok = true ∧
    work0331.jac.invOK = true ∧ acceptsUnitSq work0331.out = true := by decide +kernel

def cell0331 : CellCertificate where
  tauBall := tau0331
  contactCenter := center0331
  contactBall := contact0331
  work := work0331
  center_sq := center_sq0331
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0331.1
  jac_ok := checks0331.2.1
  accepted := checks0331.2.2

def tau0332 : RatBall :=
  ⟨⟨1/80, 21/80⟩, 3/160⟩
def center0332 : GaussianRat :=
  ⟨4665703/500000000, 93227751/500000000⟩
def contact0332 : RatBall := localContactBall tau0332 center0332
def work0332 : RoundedTauEval :=
  evalTau precision tau0332 contact0332 logTwoBall

theorem center_sq0332 : (center0332.re : ℝ)^2 +
    (center0332.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0332]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0332 : work0332.theta.ok = true ∧
    work0332.jac.invOK = true ∧ acceptsUnitSq work0332.out = true := by decide +kernel

def cell0332 : CellCertificate where
  tauBall := tau0332
  contactCenter := center0332
  contactBall := contact0332
  work := work0332
  center_sq := center_sq0332
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0332.1
  jac_ok := checks0332.2.1
  accepted := checks0332.2.2

def tau0333 : RatBall :=
  ⟨⟨3/80, 21/80⟩, 3/160⟩
def center0333 : GaussianRat :=
  ⟨27977261/1000000000, 186182371/1000000000⟩
def contact0333 : RatBall := localContactBall tau0333 center0333
def work0333 : RoundedTauEval :=
  evalTau precision tau0333 contact0333 logTwoBall

theorem center_sq0333 : (center0333.re : ℝ)^2 +
    (center0333.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0333]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0333 : work0333.theta.ok = true ∧
    work0333.jac.invOK = true ∧ acceptsUnitSq work0333.out = true := by decide +kernel

def cell0333 : CellCertificate where
  tauBall := tau0333
  contactCenter := center0333
  contactBall := contact0333
  work := work0333
  center_sq := center_sq0333
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0333.1
  jac_ok := checks0333.2.1
  accepted := checks0333.2.2

def tau0334 : RatBall :=
  ⟨⟨1/80, 23/80⟩, 3/160⟩
def center0334 : GaussianRat :=
  ⟨4738451/500000000, 102628961/500000000⟩
def contact0334 : RatBall := localContactBall tau0334 center0334
def work0334 : RoundedTauEval :=
  evalTau precision tau0334 contact0334 logTwoBall

theorem center_sq0334 : (center0334.re : ℝ)^2 +
    (center0334.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0334]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0334 : work0334.theta.ok = true ∧
    work0334.jac.invOK = true ∧ acceptsUnitSq work0334.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0041


