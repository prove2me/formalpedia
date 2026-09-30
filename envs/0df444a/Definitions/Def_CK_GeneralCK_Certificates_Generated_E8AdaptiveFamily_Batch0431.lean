-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0431
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0431
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:31:34.801325+00:00
-- url     : https://prove2.me/theorems/5b95d2f6-3930-436a-9e77-137c58158650
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0431.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0431_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3454 : work3454.theta.ok = true ∧
    work3454.jac.invOK = true ∧ acceptsUnitSq work3454.out = true := by decide +kernel

def cell3454 : CellCertificate where
  tauBall := tau3454
  contactCenter := center3454
  contactBall := contact3454
  work := work3454
  center_sq := center_sq3454
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3454.1
  jac_ok := checks3454.2.1
  accepted := checks3454.2.2

def tau3455 : RatBall :=
  ⟨⟨-5/128, 247/640⟩, 3/1280⟩
def center3455 : GaussianRat :=
  ⟨-7997111/250000000, 282149129/1000000000⟩
def contact3455 : RatBall := localContactBall tau3455 center3455
def work3455 : RoundedTauEval :=
  evalTau precision tau3455 contact3455 logTwoBall

theorem center_sq3455 : (center3455.re : ℝ)^2 +
    (center3455.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3455]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3455 : work3455.theta.ok = true ∧
    work3455.jac.invOK = true ∧ acceptsUnitSq work3455.out = true := by decide +kernel

def cell3455 : CellCertificate where
  tauBall := tau3455
  contactCenter := center3455
  contactBall := contact3455
  work := work3455
  center_sq := center_sq3455
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3455.1
  jac_ok := checks3455.2.1
  accepted := checks3455.2.2

def cells : List CellCertificate := [cell3448, cell3449, cell3450, cell3451, cell3452, cell3453, cell3454, cell3455]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431


