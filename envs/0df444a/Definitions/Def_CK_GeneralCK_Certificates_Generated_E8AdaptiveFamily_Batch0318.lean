-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0318
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0318
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:10:29.007954+00:00
-- url     : https://prove2.me/theorems/c872a48e-8727-4239-8f72-e408808ee488
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0318.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0318_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2550 : (center2550.re : ℝ)^2 +
    (center2550.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2550]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2550 : work2550.theta.ok = true ∧
    work2550.jac.invOK = true ∧ acceptsUnitSq work2550.out = true := by decide +kernel

def cell2550 : CellCertificate where
  tauBall := tau2550
  contactCenter := center2550
  contactBall := contact2550
  work := work2550
  center_sq := center_sq2550
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2550.1
  jac_ok := checks2550.2.1
  accepted := checks2550.2.2

def tau2551 : RatBall :=
  ⟨⟨13/64, 21/64⟩, 3/640⟩
def center2551 : GaussianRat :=
  ⟨30978099/200000000, 224898511/1000000000⟩
def contact2551 : RatBall := localContactBall tau2551 center2551
def work2551 : RoundedTauEval :=
  evalTau precision tau2551 contact2551 logTwoBall

theorem center_sq2551 : (center2551.re : ℝ)^2 +
    (center2551.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2551]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2551 : work2551.theta.ok = true ∧
    work2551.jac.invOK = true ∧ acceptsUnitSq work2551.out = true := by decide +kernel

def cell2551 : CellCertificate where
  tauBall := tau2551
  contactCenter := center2551
  contactBall := contact2551
  work := work2551
  center_sq := center_sq2551
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2551.1
  jac_ok := checks2551.2.1
  accepted := checks2551.2.2

def cells : List CellCertificate := [cell2544, cell2545, cell2546, cell2547, cell2548, cell2549, cell2550, cell2551]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318


