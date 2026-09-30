-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0187_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0187_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:05:06.011544+00:00
-- url     : https://prove2.me/theorems/89906fc3-20d5-490a-a7db-e47cb1553ad1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187 (part 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187 (part 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187 (part 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187 (part 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0187 (part 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1496 : RatBall :=
  ⟨⟨-3/320, -123/320⟩, 3/640⟩
def center1496 : GaussianRat :=
  ⟨-3836831/500000000, -281424629/1000000000⟩
def contact1496 : RatBall := localContactBall tau1496 center1496
def work1496 : RoundedTauEval :=
  evalTau precision tau1496 contact1496 logTwoBall

theorem center_sq1496 : (center1496.re : ℝ)^2 +
    (center1496.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1496]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1496 : work1496.theta.ok = true ∧
    work1496.jac.invOK = true ∧ acceptsUnitSq work1496.out = true := by decide +kernel

def cell1496 : CellCertificate where
  tauBall := tau1496
  contactCenter := center1496
  contactBall := contact1496
  work := work1496
  center_sq := center_sq1496
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1496.1
  jac_ok := checks1496.2.1
  accepted := checks1496.2.2

def tau1497 : RatBall :=
  ⟨⟨-1/320, -123/320⟩, 3/640⟩
def center1497 : GaussianRat :=
  ⟨-2558027/1000000000, -14072733/50000000⟩
def contact1497 : RatBall := localContactBall tau1497 center1497
def work1497 : RoundedTauEval :=
  evalTau precision tau1497 contact1497 logTwoBall

theorem center_sq1497 : (center1497.re : ℝ)^2 +
    (center1497.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1497]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1497 : work1497.theta.ok = true ∧
    work1497.jac.invOK = true ∧ acceptsUnitSq work1497.out = true := by decide +kernel

def cell1497 : CellCertificate where
  tauBall := tau1497
  contactCenter := center1497
  contactBall := contact1497
  work := work1497
  center_sq := center_sq1497
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1497.1
  jac_ok := checks1497.2.1
  accepted := checks1497.2.2

def tau1498 : RatBall :=
  ⟨⟨-3/320, -121/320⟩, 3/640⟩
def center1498 : GaussianRat :=
  ⟨-1907311/250000000, -69081087/250000000⟩
def contact1498 : RatBall := localContactBall tau1498 center1498
def work1498 : RoundedTauEval :=
  evalTau precision tau1498 contact1498 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187


