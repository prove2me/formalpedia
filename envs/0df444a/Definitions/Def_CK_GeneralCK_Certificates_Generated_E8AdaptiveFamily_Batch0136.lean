-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0136
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0136
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:34:20.753802+00:00
-- url     : https://prove2.me/theorems/0e74d2ec-500f-49c6-a19b-a929aa464bee
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0136.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0136_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1094 : work1094.theta.ok = true ∧
    work1094.jac.invOK = true ∧ acceptsUnitSq work1094.out = true := by decide +kernel

def cell1094 : CellCertificate where
  tauBall := tau1094
  contactCenter := center1094
  contactBall := contact1094
  work := work1094
  center_sq := center_sq1094
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1094.1
  jac_ok := checks1094.2.1
  accepted := checks1094.2.2

def tau1095 : RatBall :=
  ⟨⟨5/32, 41/160⟩, 3/320⟩
def center1095 : GaussianRat :=
  ⟨114906151/1000000000, 176804909/1000000000⟩
def contact1095 : RatBall := localContactBall tau1095 center1095
def work1095 : RoundedTauEval :=
  evalTau precision tau1095 contact1095 logTwoBall

theorem center_sq1095 : (center1095.re : ℝ)^2 +
    (center1095.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1095]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1095 : work1095.theta.ok = true ∧
    work1095.jac.invOK = true ∧ acceptsUnitSq work1095.out = true := by decide +kernel

def cell1095 : CellCertificate where
  tauBall := tau1095
  contactCenter := center1095
  contactBall := contact1095
  work := work1095
  center_sq := center_sq1095
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1095.1
  jac_ok := checks1095.2.1
  accepted := checks1095.2.2

def cells : List CellCertificate := [cell1088, cell1089, cell1090, cell1091, cell1092, cell1093, cell1094, cell1095]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136


