-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0160_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0160_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:46:42.908692+00:00
-- url     : https://prove2.me/theorems/02adf0f4-e324-47e4-906b-cb4f53b10343
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0160 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0160_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center1285 : GaussianRat :=
  ⟨-97111567/500000000, -37439051/200000000⟩
def contact1285 : RatBall := localContactBall tau1285 center1285
def work1285 : RoundedTauEval :=
  evalTau precision tau1285 contact1285 logTwoBall

theorem center_sq1285 : (center1285.re : ℝ)^2 +
    (center1285.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1285]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1285 : work1285.theta.ok = true ∧
    work1285.jac.invOK = true ∧ acceptsUnitSq work1285.out = true := by decide +kernel

def cell1285 : CellCertificate where
  tauBall := tau1285
  contactCenter := center1285
  contactBall := contact1285
  work := work1285
  center_sq := center_sq1285
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1285.1
  jac_ok := checks1285.2.1
  accepted := checks1285.2.2

def tau1286 : RatBall :=
  ⟨⟨-87/320, -89/320⟩, 3/640⟩
def center1286 : GaussianRat :=
  ⟨-7912299/40000000, -91131277/500000000⟩
def contact1286 : RatBall := localContactBall tau1286 center1286
def work1286 : RoundedTauEval :=
  evalTau precision tau1286 contact1286 logTwoBall

theorem center_sq1286 : (center1286.re : ℝ)^2 +
    (center1286.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1286]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1286 : work1286.theta.ok = true ∧
    work1286.jac.invOK = true ∧ acceptsUnitSq work1286.out = true := by decide +kernel

def cell1286 : CellCertificate where
  tauBall := tau1286
  contactCenter := center1286
  contactBall := contact1286
  work := work1286
  center_sq := center_sq1286
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1286.1
  jac_ok := checks1286.2.1
  accepted := checks1286.2.2

def tau1287 : RatBall :=
  ⟨⟨-17/64, -89/320⟩, 3/640⟩
def center1287 : GaussianRat :=
  ⟨-24194269/125000000, -5716477/31250000⟩
def contact1287 : RatBall := localContactBall tau1287 center1287
def work1287 : RoundedTauEval :=
  evalTau precision tau1287 contact1287 logTwoBall

theorem center_sq1287 : (center1287.re : ℝ)^2 +
    (center1287.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1287]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160


