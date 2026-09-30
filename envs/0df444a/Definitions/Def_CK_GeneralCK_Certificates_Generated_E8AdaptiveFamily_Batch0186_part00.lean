-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0186_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0186_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:07:21.707003+00:00
-- url     : https://prove2.me/theorems/220d5f78-2b1e-40e9-b25c-4ad394442df4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186 (part 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186 (part 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186 (part 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186 (part 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0186 (part 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1488 : RatBall :=
  ⟨⟨-13/320, -121/320⟩, 3/640⟩
def center1488 : GaussianRat :=
  ⟨-8256217/250000000, -34467723/125000000⟩
def contact1488 : RatBall := localContactBall tau1488 center1488
def work1488 : RoundedTauEval :=
  evalTau precision tau1488 contact1488 logTwoBall

theorem center_sq1488 : (center1488.re : ℝ)^2 +
    (center1488.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1488]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1488 : work1488.theta.ok = true ∧
    work1488.jac.invOK = true ∧ acceptsUnitSq work1488.out = true := by decide +kernel

def cell1488 : CellCertificate where
  tauBall := tau1488
  contactCenter := center1488
  contactBall := contact1488
  work := work1488
  center_sq := center_sq1488
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1488.1
  jac_ok := checks1488.2.1
  accepted := checks1488.2.2

def tau1489 : RatBall :=
  ⟨⟨-9/320, -123/320⟩, 3/640⟩
def center1489 : GaussianRat :=
  ⟨-11504853/500000000, -2811547/10000000⟩
def contact1489 : RatBall := localContactBall tau1489 center1489
def work1489 : RoundedTauEval :=
  evalTau precision tau1489 contact1489 logTwoBall

theorem center_sq1489 : (center1489.re : ℝ)^2 +
    (center1489.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1489]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1489 : work1489.theta.ok = true ∧
    work1489.jac.invOK = true ∧ acceptsUnitSq work1489.out = true := by decide +kernel

def cell1489 : CellCertificate where
  tauBall := tau1489
  contactCenter := center1489
  contactBall := contact1489
  work := work1489
  center_sq := center_sq1489
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1489.1
  jac_ok := checks1489.2.1
  accepted := checks1489.2.2

def tau1490 : RatBall :=
  ⟨⟨-11/320, -121/320⟩, 3/640⟩
def center1490 : GaussianRat :=
  ⟨-27953037/1000000000, -55183249/200000000⟩
def contact1490 : RatBall := localContactBall tau1490 center1490
def work1490 : RoundedTauEval :=
  evalTau precision tau1490 contact1490 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186


