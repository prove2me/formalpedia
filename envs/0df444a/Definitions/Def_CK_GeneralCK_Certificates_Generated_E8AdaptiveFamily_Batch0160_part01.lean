-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0160_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0160_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:09:53.710264+00:00
-- url     : https://prove2.me/theorems/9606fded-1038-45c5-92eb-5598d6b62f81
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0160 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0160_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1282 : (center1282.re : ℝ)^2 +
    (center1282.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1282]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1282 : work1282.theta.ok = true ∧
    work1282.jac.invOK = true ∧ acceptsUnitSq work1282.out = true := by decide +kernel

def cell1282 : CellCertificate where
  tauBall := tau1282
  contactCenter := center1282
  contactBall := contact1282
  work := work1282
  center_sq := center_sq1282
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1282.1
  jac_ok := checks1282.2.1
  accepted := checks1282.2.2

def tau1283 : RatBall :=
  ⟨⟨-81/320, -93/320⟩, 3/640⟩
def center1283 : GaussianRat :=
  ⟨-93152319/500000000, -24105877/125000000⟩
def contact1283 : RatBall := localContactBall tau1283 center1283
def work1283 : RoundedTauEval :=
  evalTau precision tau1283 contact1283 logTwoBall

theorem center_sq1283 : (center1283.re : ℝ)^2 +
    (center1283.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1283]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1283 : work1283.theta.ok = true ∧
    work1283.jac.invOK = true ∧ acceptsUnitSq work1283.out = true := by decide +kernel

def cell1283 : CellCertificate where
  tauBall := tau1283
  contactCenter := center1283
  contactBall := contact1283
  work := work1283
  center_sq := center_sq1283
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1283.1
  jac_ok := checks1283.2.1
  accepted := checks1283.2.2

def tau1284 : RatBall :=
  ⟨⟨-87/320, -91/320⟩, 3/640⟩
def center1284 : GaussianRat :=
  ⟨-49621711/250000000, -186511513/1000000000⟩
def contact1284 : RatBall := localContactBall tau1284 center1284
def work1284 : RoundedTauEval :=
  evalTau precision tau1284 contact1284 logTwoBall

theorem center_sq1284 : (center1284.re : ℝ)^2 +
    (center1284.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1284]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1284 : work1284.theta.ok = true ∧
    work1284.jac.invOK = true ∧ acceptsUnitSq work1284.out = true := by decide +kernel

def cell1284 : CellCertificate where
  tauBall := tau1284
  contactCenter := center1284
  contactBall := contact1284
  work := work1284
  center_sq := center_sq1284
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1284.1
  jac_ok := checks1284.2.1
  accepted := checks1284.2.2

def tau1285 : RatBall :=
  ⟨⟨-17/64, -91/320⟩, 3/640⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160


