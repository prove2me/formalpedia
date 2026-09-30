-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0423
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0423
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:04:28.721451+00:00
-- url     : https://prove2.me/theorems/63255378-ead4-447b-9669-0018c6360e96
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0423.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0423_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3390 : RoundedTauEval :=
  evalTau precision tau3390 contact3390 logTwoBall

theorem center_sq3390 : (center3390.re : ℝ)^2 +
    (center3390.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3390]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3390 : work3390.theta.ok = true ∧
    work3390.jac.invOK = true ∧ acceptsUnitSq work3390.out = true := by decide +kernel

def cell3390 : CellCertificate where
  tauBall := tau3390
  contactCenter := center3390
  contactBall := contact3390
  work := work3390
  center_sq := center_sq3390
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3390.1
  jac_ok := checks3390.2.1
  accepted := checks3390.2.2

def tau3391 : RatBall :=
  ⟨⟨-51/640, 247/640⟩, 3/1280⟩
def center3391 : GaussianRat :=
  ⟨-32518989/500000000, 70076353/250000000⟩
def contact3391 : RatBall := localContactBall tau3391 center3391
def work3391 : RoundedTauEval :=
  evalTau precision tau3391 contact3391 logTwoBall

theorem center_sq3391 : (center3391.re : ℝ)^2 +
    (center3391.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3391]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3391 : work3391.theta.ok = true ∧
    work3391.jac.invOK = true ∧ acceptsUnitSq work3391.out = true := by decide +kernel

def cell3391 : CellCertificate where
  tauBall := tau3391
  contactCenter := center3391
  contactBall := contact3391
  work := work3391
  center_sq := center_sq3391
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3391.1
  jac_ok := checks3391.2.1
  accepted := checks3391.2.2

def cells : List CellCertificate := [cell3384, cell3385, cell3386, cell3387, cell3388, cell3389, cell3390, cell3391]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423


