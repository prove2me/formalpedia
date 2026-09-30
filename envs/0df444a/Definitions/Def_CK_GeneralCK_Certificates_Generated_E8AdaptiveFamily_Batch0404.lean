-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0404
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0404
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:41:52.51957+00:00
-- url     : https://prove2.me/theorems/9bfa07ec-5859-444b-be47-0268025c4136
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0404.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0404_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact3238 : RatBall := localContactBall tau3238 center3238
def work3238 : RoundedTauEval :=
  evalTau precision tau3238 contact3238 logTwoBall

theorem center_sq3238 : (center3238.re : ℝ)^2 +
    (center3238.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3238]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3238 : work3238.theta.ok = true ∧
    work3238.jac.invOK = true ∧ acceptsUnitSq work3238.out = true := by decide +kernel

def cell3238 : CellCertificate where
  tauBall := tau3238
  contactCenter := center3238
  contactBall := contact3238
  work := work3238
  center_sq := center_sq3238
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3238.1
  jac_ok := checks3238.2.1
  accepted := checks3238.2.2

def tau3239 : RatBall :=
  ⟨⟨-23/128, 229/640⟩, 3/1280⟩
def center3239 : GaussianRat :=
  ⟨-70397387/500000000, 249469121/1000000000⟩
def contact3239 : RatBall := localContactBall tau3239 center3239
def work3239 : RoundedTauEval :=
  evalTau precision tau3239 contact3239 logTwoBall

theorem center_sq3239 : (center3239.re : ℝ)^2 +
    (center3239.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3239]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3239 : work3239.theta.ok = true ∧
    work3239.jac.invOK = true ∧ acceptsUnitSq work3239.out = true := by decide +kernel

def cell3239 : CellCertificate where
  tauBall := tau3239
  contactCenter := center3239
  contactBall := contact3239
  work := work3239
  center_sq := center_sq3239
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3239.1
  jac_ok := checks3239.2.1
  accepted := checks3239.2.2

def cells : List CellCertificate := [cell3232, cell3233, cell3234, cell3235, cell3236, cell3237, cell3238, cell3239]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404


