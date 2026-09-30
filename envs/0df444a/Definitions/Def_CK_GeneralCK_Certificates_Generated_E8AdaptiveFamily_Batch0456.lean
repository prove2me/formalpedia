-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0456
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0456
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:06:44.91044+00:00
-- url     : https://prove2.me/theorems/f7dd6935-18ca-4ee1-b9af-f86c784669a2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0456` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0456` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0456` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0456 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0456.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0456_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0456

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center3654 : GaussianRat :=
  ⟨32518989/500000000, 70076353/250000000⟩
def contact3654 : RatBall := localContactBall tau3654 center3654
def work3654 : RoundedTauEval :=
  evalTau precision tau3654 contact3654 logTwoBall

theorem center_sq3654 : (center3654.re : ℝ)^2 +
    (center3654.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3654]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3654 : work3654.theta.ok = true ∧
    work3654.jac.invOK = true ∧ acceptsUnitSq work3654.out = true := by decide +kernel

def cell3654 : CellCertificate where
  tauBall := tau3654
  contactCenter := center3654
  contactBall := contact3654
  work := work3654
  center_sq := center_sq3654
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3654.1
  jac_ok := checks3654.2.1
  accepted := checks3654.2.2

def tau3655 : RatBall :=
  ⟨⟨53/640, 49/128⟩, 3/1280⟩
def center3655 : GaussianRat :=
  ⟨4210637/62500000, 55518211/200000000⟩
def contact3655 : RatBall := localContactBall tau3655 center3655
def work3655 : RoundedTauEval :=
  evalTau precision tau3655 contact3655 logTwoBall

theorem center_sq3655 : (center3655.re : ℝ)^2 +
    (center3655.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3655]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3655 : work3655.theta.ok = true ∧
    work3655.jac.invOK = true ∧ acceptsUnitSq work3655.out = true := by decide +kernel

def cell3655 : CellCertificate where
  tauBall := tau3655
  contactCenter := center3655
  contactBall := contact3655
  work := work3655
  center_sq := center_sq3655
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3655.1
  jac_ok := checks3655.2.1
  accepted := checks3655.2.2

def cells : List CellCertificate := [cell3648, cell3649, cell3650, cell3651, cell3652, cell3653, cell3654, cell3655]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0456


