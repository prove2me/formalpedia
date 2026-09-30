-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0181
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0181
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:37:35.191507+00:00
-- url     : https://prove2.me/theorems/fd6203b8-18d5-4dac-8697-c79c95acc0b2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0181` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0181` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0181` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0181 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0181.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0181_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0181

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact1454 : RatBall := localContactBall tau1454 center1454
def work1454 : RoundedTauEval :=
  evalTau precision tau1454 contact1454 logTwoBall

theorem center_sq1454 : (center1454.re : ℝ)^2 +
    (center1454.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1454]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1454 : work1454.theta.ok = true ∧
    work1454.jac.invOK = true ∧ acceptsUnitSq work1454.out = true := by decide +kernel

def cell1454 : CellCertificate where
  tauBall := tau1454
  contactCenter := center1454
  contactBall := contact1454
  work := work1454
  center_sq := center_sq1454
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1454.1
  jac_ok := checks1454.2.1
  accepted := checks1454.2.2

def tau1455 : RatBall :=
  ⟨⟨-31/320, -119/320⟩, 3/640⟩
def center1455 : GaussianRat :=
  ⟨-77908577/1000000000, -267922911/1000000000⟩
def contact1455 : RatBall := localContactBall tau1455 center1455
def work1455 : RoundedTauEval :=
  evalTau precision tau1455 contact1455 logTwoBall

theorem center_sq1455 : (center1455.re : ℝ)^2 +
    (center1455.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1455]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1455 : work1455.theta.ok = true ∧
    work1455.jac.invOK = true ∧ acceptsUnitSq work1455.out = true := by decide +kernel

def cell1455 : CellCertificate where
  tauBall := tau1455
  contactCenter := center1455
  contactBall := contact1455
  work := work1455
  center_sq := center_sq1455
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1455.1
  jac_ok := checks1455.2.1
  accepted := checks1455.2.2

def cells : List CellCertificate := [cell1448, cell1449, cell1450, cell1451, cell1452, cell1453, cell1454, cell1455]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0181


