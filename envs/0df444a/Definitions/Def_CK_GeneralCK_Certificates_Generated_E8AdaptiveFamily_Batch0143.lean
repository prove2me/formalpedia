-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0143
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0143
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:17:00.462863+00:00
-- url     : https://prove2.me/theorems/e36a1623-d502-4e16-8379-52cf75ddbe4f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0143.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0143_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1150 : RatBall :=
  ⟨⟨27/160, 49/160⟩, 3/320⟩
def center1150 : GaussianRat :=
  ⟨3988651/31250000, 53050431/250000000⟩
def contact1150 : RatBall := localContactBall tau1150 center1150
def work1150 : RoundedTauEval :=
  evalTau precision tau1150 contact1150 logTwoBall

theorem center_sq1150 : (center1150.re : ℝ)^2 +
    (center1150.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1150]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1150 : work1150.theta.ok = true ∧
    work1150.jac.invOK = true ∧ acceptsUnitSq work1150.out = true := by decide +kernel

def cell1150 : CellCertificate where
  tauBall := tau1150
  contactCenter := center1150
  contactBall := contact1150
  work := work1150
  center_sq := center_sq1150
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1150.1
  jac_ok := checks1150.2.1
  accepted := checks1150.2.2

def tau1151 : RatBall :=
  ⟨⟨33/160, 33/160⟩, 3/320⟩
def center1151 : GaussianRat :=
  ⟨73472183/500000000, 69270487/500000000⟩
def contact1151 : RatBall := localContactBall tau1151 center1151
def work1151 : RoundedTauEval :=
  evalTau precision tau1151 contact1151 logTwoBall

theorem center_sq1151 : (center1151.re : ℝ)^2 +
    (center1151.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1151]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1151 : work1151.theta.ok = true ∧
    work1151.jac.invOK = true ∧ acceptsUnitSq work1151.out = true := by decide +kernel

def cell1151 : CellCertificate where
  tauBall := tau1151
  contactCenter := center1151
  contactBall := contact1151
  work := work1151
  center_sq := center_sq1151
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1151.1
  jac_ok := checks1151.2.1
  accepted := checks1151.2.2

def cells : List CellCertificate := [cell1144, cell1145, cell1146, cell1147, cell1148, cell1149, cell1150, cell1151]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143


