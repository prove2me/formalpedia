-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0185
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0185
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:01:08.979079+00:00
-- url     : https://prove2.me/theorems/3c31ddb9-c961-4851-8409-904df6d06778
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0185.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0185_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center1486 : GaussianRat :=
  ⟨-42220551/1000000000, -25529699/100000000⟩
def contact1486 : RatBall := localContactBall tau1486 center1486
def work1486 : RoundedTauEval :=
  evalTau precision tau1486 contact1486 logTwoBall

theorem center_sq1486 : (center1486.re : ℝ)^2 +
    (center1486.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1486]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1486 : work1486.theta.ok = true ∧
    work1486.jac.invOK = true ∧ acceptsUnitSq work1486.out = true := by decide +kernel

def cell1486 : CellCertificate where
  tauBall := tau1486
  contactCenter := center1486
  contactBall := contact1486
  work := work1486
  center_sq := center_sq1486
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1486.1
  jac_ok := checks1486.2.1
  accepted := checks1486.2.2

def tau1487 : RatBall :=
  ⟨⟨-3/64, -121/320⟩, 3/640⟩
def center1487 : GaussianRat :=
  ⟨-38091451/1000000000, -137769289/500000000⟩
def contact1487 : RatBall := localContactBall tau1487 center1487
def work1487 : RoundedTauEval :=
  evalTau precision tau1487 contact1487 logTwoBall

theorem center_sq1487 : (center1487.re : ℝ)^2 +
    (center1487.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1487]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1487 : work1487.theta.ok = true ∧
    work1487.jac.invOK = true ∧ acceptsUnitSq work1487.out = true := by decide +kernel

def cell1487 : CellCertificate where
  tauBall := tau1487
  contactCenter := center1487
  contactBall := contact1487
  work := work1487
  center_sq := center_sq1487
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1487.1
  jac_ok := checks1487.2.1
  accepted := checks1487.2.2

def cells : List CellCertificate := [cell1480, cell1481, cell1482, cell1483, cell1484, cell1485, cell1486, cell1487]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185


