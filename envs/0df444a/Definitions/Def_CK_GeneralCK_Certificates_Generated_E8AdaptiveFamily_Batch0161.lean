-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0161
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0161
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:21:21.62555+00:00
-- url     : https://prove2.me/theorems/f0c9c04a-8afd-464a-a836-ef87af996ae6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0161.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0161_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1293 : RoundedTauEval :=
  evalTau precision tau1293 contact1293 logTwoBall

theorem center_sq1293 : (center1293.re : ℝ)^2 +
    (center1293.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1293]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1293 : work1293.theta.ok = true ∧
    work1293.jac.invOK = true ∧ acceptsUnitSq work1293.out = true := by decide +kernel

def cell1293 : CellCertificate where
  tauBall := tau1293
  contactCenter := center1293
  contactBall := contact1293
  work := work1293
  center_sq := center_sq1293
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1293.1
  jac_ok := checks1293.2.1
  accepted := checks1293.2.2

def tau1294 : RatBall :=
  ⟨⟨-19/64, -17/64⟩, 3/640⟩
def center1294 : GaussianRat :=
  ⟨-42650399/200000000, -171191029/1000000000⟩
def contact1294 : RatBall := localContactBall tau1294 center1294
def work1294 : RoundedTauEval :=
  evalTau precision tau1294 contact1294 logTwoBall

theorem center_sq1294 : (center1294.re : ℝ)^2 +
    (center1294.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1294]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1294 : work1294.theta.ok = true ∧
    work1294.jac.invOK = true ∧ acceptsUnitSq work1294.out = true := by decide +kernel

def cell1294 : CellCertificate where
  tauBall := tau1294
  contactCenter := center1294
  contactBall := contact1294
  work := work1294
  center_sq := center_sq1294
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1294.1
  jac_ok := checks1294.2.1
  accepted := checks1294.2.2

def tau1295 : RatBall :=
  ⟨⟨-93/320, -17/64⟩, 3/640⟩
def center1295 : GaussianRat :=
  ⟨-104546899/500000000, -171855447/1000000000⟩
def contact1295 : RatBall := localContactBall tau1295 center1295
def work1295 : RoundedTauEval :=
  evalTau precision tau1295 contact1295 logTwoBall

theorem center_sq1295 : (center1295.re : ℝ)^2 +
    (center1295.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1295]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1295 : work1295.theta.ok = true ∧
    work1295.jac.invOK = true ∧ acceptsUnitSq work1295.out = true := by decide +kernel

def cell1295 : CellCertificate where
  tauBall := tau1295
  contactCenter := center1295
  contactBall := contact1295
  work := work1295
  center_sq := center_sq1295
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1295.1
  jac_ok := checks1295.2.1
  accepted := checks1295.2.2

def cells : List CellCertificate := [cell1288, cell1289, cell1290, cell1291, cell1292, cell1293, cell1294, cell1295]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161


