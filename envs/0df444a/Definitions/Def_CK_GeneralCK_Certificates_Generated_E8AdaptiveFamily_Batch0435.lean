-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0435
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0435
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:37:29.401989+00:00
-- url     : https://prove2.me/theorems/3d31cec4-a149-4546-a3ce-52ac03f6edb2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0435` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0435` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0435` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0435 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0435.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0435_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0435

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact3486 : RatBall := localContactBall tau3486 center3486
def work3486 : RoundedTauEval :=
  evalTau precision tau3486 contact3486 logTwoBall

theorem center_sq3486 : (center3486.re : ℝ)^2 +
    (center3486.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3486]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3486 : work3486.theta.ok = true ∧
    work3486.jac.invOK = true ∧ acceptsUnitSq work3486.out = true := by decide +kernel

def cell3486 : CellCertificate where
  tauBall := tau3486
  contactCenter := center3486
  contactBall := contact3486
  work := work3486
  center_sq := center_sq3486
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3486.1
  jac_ok := checks3486.2.1
  accepted := checks3486.2.2

def tau3487 : RatBall :=
  ⟨⟨-21/640, 51/128⟩, 3/1280⟩
def center3487 : GaussianRat :=
  ⟨-27204153/1000000000, 58521471/200000000⟩
def contact3487 : RatBall := localContactBall tau3487 center3487
def work3487 : RoundedTauEval :=
  evalTau precision tau3487 contact3487 logTwoBall

theorem center_sq3487 : (center3487.re : ℝ)^2 +
    (center3487.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3487]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3487 : work3487.theta.ok = true ∧
    work3487.jac.invOK = true ∧ acceptsUnitSq work3487.out = true := by decide +kernel

def cell3487 : CellCertificate where
  tauBall := tau3487
  contactCenter := center3487
  contactBall := contact3487
  work := work3487
  center_sq := center_sq3487
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3487.1
  jac_ok := checks3487.2.1
  accepted := checks3487.2.2

def cells : List CellCertificate := [cell3480, cell3481, cell3482, cell3483, cell3484, cell3485, cell3486, cell3487]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0435


