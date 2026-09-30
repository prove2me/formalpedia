-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0137
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0137
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:33:19.163166+00:00
-- url     : https://prove2.me/theorems/f9478699-49a8-42b2-9fef-05ed0f710e5b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0137` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0137` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0137` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0137 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0137.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0137_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0137

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1102 : work1102.theta.ok = true ∧
    work1102.jac.invOK = true ∧ acceptsUnitSq work1102.out = true := by decide +kernel

def cell1102 : CellCertificate where
  tauBall := tau1102
  contactCenter := center1102
  contactBall := contact1102
  work := work1102
  center_sq := center_sq1102
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1102.1
  jac_ok := checks1102.2.1
  accepted := checks1102.2.2

def tau1103 : RatBall :=
  ⟨⟨5/32, 9/32⟩, 3/320⟩
def center1103 : GaussianRat :=
  ⟨116565793/1000000000, 194890619/1000000000⟩
def contact1103 : RatBall := localContactBall tau1103 center1103
def work1103 : RoundedTauEval :=
  evalTau precision tau1103 contact1103 logTwoBall

theorem center_sq1103 : (center1103.re : ℝ)^2 +
    (center1103.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1103]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1103 : work1103.theta.ok = true ∧
    work1103.jac.invOK = true ∧ acceptsUnitSq work1103.out = true := by decide +kernel

def cell1103 : CellCertificate where
  tauBall := tau1103
  contactCenter := center1103
  contactBall := contact1103
  work := work1103
  center_sq := center_sq1103
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1103.1
  jac_ok := checks1103.2.1
  accepted := checks1103.2.2

def cells : List CellCertificate := [cell1096, cell1097, cell1098, cell1099, cell1100, cell1101, cell1102, cell1103]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0137


