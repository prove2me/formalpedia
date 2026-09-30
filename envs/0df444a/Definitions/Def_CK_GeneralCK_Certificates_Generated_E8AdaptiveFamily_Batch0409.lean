-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0409
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0409
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:45:14.477237+00:00
-- url     : https://prove2.me/theorems/8413fc88-a5ba-4cf7-8eec-beea2dad5aa6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0409.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0409_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell3277 : CellCertificate where
  tauBall := tau3277
  contactCenter := center3277
  contactBall := contact3277
  work := work3277
  center_sq := center_sq3277
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3277.1
  jac_ok := checks3277.2.1
  accepted := checks3277.2.2

def tau3278 : RatBall :=
  ⟨⟨-93/640, 231/640⟩, 3/1280⟩
def center3278 : GaussianRat :=
  ⟨-114923139/1000000000, 12769801/50000000⟩
def contact3278 : RatBall := localContactBall tau3278 center3278
def work3278 : RoundedTauEval :=
  evalTau precision tau3278 contact3278 logTwoBall

theorem center_sq3278 : (center3278.re : ℝ)^2 +
    (center3278.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3278]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3278 : work3278.theta.ok = true ∧
    work3278.jac.invOK = true ∧ acceptsUnitSq work3278.out = true := by decide +kernel

def cell3278 : CellCertificate where
  tauBall := tau3278
  contactCenter := center3278
  contactBall := contact3278
  work := work3278
  center_sq := center_sq3278
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3278.1
  jac_ok := checks3278.2.1
  accepted := checks3278.2.2

def tau3279 : RatBall :=
  ⟨⟨-19/128, 233/640⟩, 3/1280⟩
def center3279 : GaussianRat :=
  ⟨-7351929/62500000, 128752067/500000000⟩
def contact3279 : RatBall := localContactBall tau3279 center3279
def work3279 : RoundedTauEval :=
  evalTau precision tau3279 contact3279 logTwoBall

theorem center_sq3279 : (center3279.re : ℝ)^2 +
    (center3279.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3279]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3279 : work3279.theta.ok = true ∧
    work3279.jac.invOK = true ∧ acceptsUnitSq work3279.out = true := by decide +kernel

def cell3279 : CellCertificate where
  tauBall := tau3279
  contactCenter := center3279
  contactBall := contact3279
  work := work3279
  center_sq := center_sq3279
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3279.1
  jac_ok := checks3279.2.1
  accepted := checks3279.2.2

def cells : List CellCertificate := [cell3272, cell3273, cell3274, cell3275, cell3276, cell3277, cell3278, cell3279]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409


