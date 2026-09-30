-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0164_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0164_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:13:14.24399+00:00
-- url     : https://prove2.me/theorems/de93c878-26d3-420c-9bfc-bf4a36c69624
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0164 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0164_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1314 : RoundedTauEval :=
  evalTau precision tau1314 contact1314 logTwoBall

theorem center_sq1314 : (center1314.re : ℝ)^2 +
    (center1314.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1314]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1314 : work1314.theta.ok = true ∧
    work1314.jac.invOK = true ∧ acceptsUnitSq work1314.out = true := by decide +kernel

def cell1314 : CellCertificate where
  tauBall := tau1314
  contactCenter := center1314
  contactBall := contact1314
  work := work1314
  center_sq := center_sq1314
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1314.1
  jac_ok := checks1314.2.1
  accepted := checks1314.2.2

def tau1315 : RatBall :=
  ⟨⟨-81/320, -17/64⟩, 3/640⟩
def center1315 : GaussianRat :=
  ⟨-36750261/200000000, -1756473/10000000⟩
def contact1315 : RatBall := localContactBall tau1315 center1315
def work1315 : RoundedTauEval :=
  evalTau precision tau1315 contact1315 logTwoBall

theorem center_sq1315 : (center1315.re : ℝ)^2 +
    (center1315.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1315]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1315 : work1315.theta.ok = true ∧
    work1315.jac.invOK = true ∧ acceptsUnitSq work1315.out = true := by decide +kernel

def cell1315 : CellCertificate where
  tauBall := tau1315
  contactCenter := center1315
  contactBall := contact1315
  work := work1315
  center_sq := center_sq1315
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1315.1
  jac_ok := checks1315.2.1
  accepted := checks1315.2.2

def tau1316 : RatBall :=
  ⟨⟨-79/320, -19/64⟩, 3/640⟩
def center1316 : GaussianRat :=
  ⟨-91322907/500000000, -98931697/500000000⟩
def contact1316 : RatBall := localContactBall tau1316 center1316
def work1316 : RoundedTauEval :=
  evalTau precision tau1316 contact1316 logTwoBall

theorem center_sq1316 : (center1316.re : ℝ)^2 +
    (center1316.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1316]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1316 : work1316.theta.ok = true ∧
    work1316.jac.invOK = true ∧ acceptsUnitSq work1316.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164


