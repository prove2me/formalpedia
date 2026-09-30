-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0197
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0197
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:50:11.31976+00:00
-- url     : https://prove2.me/theorems/d0ef6e0c-f5e2-4932-ae9d-4829738fc045
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0197.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0197_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1582 : (center1582.re : ℝ)^2 +
    (center1582.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1582]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1582 : work1582.theta.ok = true ∧
    work1582.jac.invOK = true ∧ acceptsUnitSq work1582.out = true := by decide +kernel

def cell1582 : CellCertificate where
  tauBall := tau1582
  contactCenter := center1582
  contactBall := contact1582
  work := work1582
  center_sq := center_sq1582
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1582.1
  jac_ok := checks1582.2.1
  accepted := checks1582.2.2

def tau1583 : RatBall :=
  ⟨⟨19/320, -121/320⟩, 3/640⟩
def center1583 : GaussianRat :=
  ⟨48205717/1000000000, -275046561/1000000000⟩
def contact1583 : RatBall := localContactBall tau1583 center1583
def work1583 : RoundedTauEval :=
  evalTau precision tau1583 contact1583 logTwoBall

theorem center_sq1583 : (center1583.re : ℝ)^2 +
    (center1583.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1583]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1583 : work1583.theta.ok = true ∧
    work1583.jac.invOK = true ∧ acceptsUnitSq work1583.out = true := by decide +kernel

def cell1583 : CellCertificate where
  tauBall := tau1583
  contactCenter := center1583
  contactBall := contact1583
  work := work1583
  center_sq := center_sq1583
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1583.1
  jac_ok := checks1583.2.1
  accepted := checks1583.2.2

def cells : List CellCertificate := [cell1576, cell1577, cell1578, cell1579, cell1580, cell1581, cell1582, cell1583]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197


