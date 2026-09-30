-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0169
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0169
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:44:48.521927+00:00
-- url     : https://prove2.me/theorems/0863961d-e6c1-401d-a662-1a8e08aae0f9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0169.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0169_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1358 : (center1358.re : ℝ)^2 +
    (center1358.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1358]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1358 : work1358.theta.ok = true ∧
    work1358.jac.invOK = true ∧ acceptsUnitSq work1358.out = true := by decide +kernel

def cell1358 : CellCertificate where
  tauBall := tau1358
  contactCenter := center1358
  contactBall := contact1358
  work := work1358
  center_sq := center_sq1358
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1358.1
  jac_ok := checks1358.2.1
  accepted := checks1358.2.2

def tau1359 : RatBall :=
  ⟨⟨-37/320, -23/64⟩, 3/640⟩
def center1359 : GaussianRat :=
  ⟨-91765617/1000000000, -12836069/50000000⟩
def contact1359 : RatBall := localContactBall tau1359 center1359
def work1359 : RoundedTauEval :=
  evalTau precision tau1359 contact1359 logTwoBall

theorem center_sq1359 : (center1359.re : ℝ)^2 +
    (center1359.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1359]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1359 : work1359.theta.ok = true ∧
    work1359.jac.invOK = true ∧ acceptsUnitSq work1359.out = true := by decide +kernel

def cell1359 : CellCertificate where
  tauBall := tau1359
  contactCenter := center1359
  contactBall := contact1359
  work := work1359
  center_sq := center_sq1359
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1359.1
  jac_ok := checks1359.2.1
  accepted := checks1359.2.2

def cells : List CellCertificate := [cell1352, cell1353, cell1354, cell1355, cell1356, cell1357, cell1358, cell1359]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169


