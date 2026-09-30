-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0142
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0142
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:31:13.060742+00:00
-- url     : https://prove2.me/theorems/a6d00524-ef2a-4560-a60d-e06526979dda
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0142` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0142` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0142` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0142 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0142.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0142_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0142

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1142 : work1142.theta.ok = true ∧
    work1142.jac.invOK = true ∧ acceptsUnitSq work1142.out = true := by decide +kernel

def cell1142 : CellCertificate where
  tauBall := tau1142
  contactCenter := center1142
  contactBall := contact1142
  work := work1142
  center_sq := center_sq1142
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1142.1
  jac_ok := checks1142.2.1
  accepted := checks1142.2.2

def tau1143 : RatBall :=
  ⟨⟨17/160, 51/160⟩, 3/320⟩
def center1143 : GaussianRat :=
  ⟨40905123/500000000, 113032697/500000000⟩
def contact1143 : RatBall := localContactBall tau1143 center1143
def work1143 : RoundedTauEval :=
  evalTau precision tau1143 contact1143 logTwoBall

theorem center_sq1143 : (center1143.re : ℝ)^2 +
    (center1143.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1143]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1143 : work1143.theta.ok = true ∧
    work1143.jac.invOK = true ∧ acceptsUnitSq work1143.out = true := by decide +kernel

def cell1143 : CellCertificate where
  tauBall := tau1143
  contactCenter := center1143
  contactBall := contact1143
  work := work1143
  center_sq := center_sq1143
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1143.1
  jac_ok := checks1143.2.1
  accepted := checks1143.2.2

def cells : List CellCertificate := [cell1136, cell1137, cell1138, cell1139, cell1140, cell1141, cell1142, cell1143]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0142


