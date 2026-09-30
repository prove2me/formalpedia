-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0315
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0315
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:57:23.110383+00:00
-- url     : https://prove2.me/theorems/cea4f430-85e8-468e-8496-2cbb96e38873
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0315` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0315` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0315` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0315 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0315.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0315_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0315

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact2526 : RatBall := localContactBall tau2526 center2526
def work2526 : RoundedTauEval :=
  evalTau precision tau2526 contact2526 logTwoBall

theorem center_sq2526 : (center2526.re : ℝ)^2 +
    (center2526.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2526]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2526 : work2526.theta.ok = true ∧
    work2526.jac.invOK = true ∧ acceptsUnitSq work2526.out = true := by decide +kernel

def cell2526 : CellCertificate where
  tauBall := tau2526
  contactCenter := center2526
  contactBall := contact2526
  work := work2526
  center_sq := center_sq2526
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2526.1
  jac_ok := checks2526.2.1
  accepted := checks2526.2.2

def tau2527 : RatBall :=
  ⟨⟨71/320, 99/320⟩, 3/640⟩
def center2527 : GaussianRat :=
  ⟨83191847/500000000, 52342851/250000000⟩
def contact2527 : RatBall := localContactBall tau2527 center2527
def work2527 : RoundedTauEval :=
  evalTau precision tau2527 contact2527 logTwoBall

theorem center_sq2527 : (center2527.re : ℝ)^2 +
    (center2527.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2527]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2527 : work2527.theta.ok = true ∧
    work2527.jac.invOK = true ∧ acceptsUnitSq work2527.out = true := by decide +kernel

def cell2527 : CellCertificate where
  tauBall := tau2527
  contactCenter := center2527
  contactBall := contact2527
  work := work2527
  center_sq := center_sq2527
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2527.1
  jac_ok := checks2527.2.1
  accepted := checks2527.2.2

def cells : List CellCertificate := [cell2520, cell2521, cell2522, cell2523, cell2524, cell2525, cell2526, cell2527]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0315


