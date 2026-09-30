-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0183
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0183
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:39:57.558227+00:00
-- url     : https://prove2.me/theorems/8471dc92-8888-4b45-8521-e70917c8a726
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0183.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0183_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact1470 : RatBall := localContactBall tau1470 center1470
def work1470 : RoundedTauEval :=
  evalTau precision tau1470 contact1470 logTwoBall

theorem center_sq1470 : (center1470.re : ℝ)^2 +
    (center1470.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1470]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1470 : work1470.theta.ok = true ∧
    work1470.jac.invOK = true ∧ acceptsUnitSq work1470.out = true := by decide +kernel

def cell1470 : CellCertificate where
  tauBall := tau1470
  contactCenter := center1470
  contactBall := contact1470
  work := work1470
  center_sq := center_sq1470
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1470.1
  jac_ok := checks1470.2.1
  accepted := checks1470.2.2

def tau1471 : RatBall :=
  ⟨⟨-23/320, -119/320⟩, 3/640⟩
def center1471 : GaussianRat :=
  ⟨-14490933/250000000, -269422101/1000000000⟩
def contact1471 : RatBall := localContactBall tau1471 center1471
def work1471 : RoundedTauEval :=
  evalTau precision tau1471 contact1471 logTwoBall

theorem center_sq1471 : (center1471.re : ℝ)^2 +
    (center1471.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1471]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1471 : work1471.theta.ok = true ∧
    work1471.jac.invOK = true ∧ acceptsUnitSq work1471.out = true := by decide +kernel

def cell1471 : CellCertificate where
  tauBall := tau1471
  contactCenter := center1471
  contactBall := contact1471
  work := work1471
  center_sq := center_sq1471
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1471.1
  jac_ok := checks1471.2.1
  accepted := checks1471.2.2

def cells : List CellCertificate := [cell1464, cell1465, cell1466, cell1467, cell1468, cell1469, cell1470, cell1471]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183


