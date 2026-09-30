-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0416
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0416
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:32:47.555092+00:00
-- url     : https://prove2.me/theorems/8230fe9a-cd98-413c-ac36-09295d303e66
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0416.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0416_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3335 : RatBall :=
  ⟨⟨-77/640, 241/640⟩, 3/1280⟩
def center3335 : GaussianRat :=
  ⟨-96833401/1000000000, 8432309/31250000⟩
def contact3335 : RatBall := localContactBall tau3335 center3335
def work3335 : RoundedTauEval :=
  evalTau precision tau3335 contact3335 logTwoBall

theorem center_sq3335 : (center3335.re : ℝ)^2 +
    (center3335.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3335]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3335 : work3335.theta.ok = true ∧
    work3335.jac.invOK = true ∧ acceptsUnitSq work3335.out = true := by decide +kernel

def cell3335 : CellCertificate where
  tauBall := tau3335
  contactCenter := center3335
  contactBall := contact3335
  work := work3335
  center_sq := center_sq3335
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3335.1
  jac_ok := checks3335.2.1
  accepted := checks3335.2.2

def cells : List CellCertificate := [cell3328, cell3329, cell3330, cell3331, cell3332, cell3333, cell3334, cell3335]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416


