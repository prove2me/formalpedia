-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0385
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0385
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:43:50.347272+00:00
-- url     : https://prove2.me/theorems/4427ab0e-1409-4ee8-9673-38c33fabd25f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0385` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0385` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0385` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0385 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0385.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0385_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0385

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3086 : RatBall :=
  ⟨⟨71/640, -239/640⟩, 3/1280⟩
def center3086 : GaussianRat :=
  ⟨89169649/1000000000, -67032703/250000000⟩
def contact3086 : RatBall := localContactBall tau3086 center3086
def work3086 : RoundedTauEval :=
  evalTau precision tau3086 contact3086 logTwoBall

theorem center_sq3086 : (center3086.re : ℝ)^2 +
    (center3086.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3086]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3086 : work3086.theta.ok = true ∧
    work3086.jac.invOK = true ∧ acceptsUnitSq work3086.out = true := by decide +kernel

def cell3086 : CellCertificate where
  tauBall := tau3086
  contactCenter := center3086
  contactBall := contact3086
  work := work3086
  center_sq := center_sq3086
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3086.1
  jac_ok := checks3086.2.1
  accepted := checks3086.2.2

def tau3087 : RatBall :=
  ⟨⟨69/640, -237/640⟩, 3/1280⟩
def center3087 : GaussianRat :=
  ⟨86460351/1000000000, -265900339/1000000000⟩
def contact3087 : RatBall := localContactBall tau3087 center3087
def work3087 : RoundedTauEval :=
  evalTau precision tau3087 contact3087 logTwoBall

theorem center_sq3087 : (center3087.re : ℝ)^2 +
    (center3087.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3087]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3087 : work3087.theta.ok = true ∧
    work3087.jac.invOK = true ∧ acceptsUnitSq work3087.out = true := by decide +kernel

def cell3087 : CellCertificate where
  tauBall := tau3087
  contactCenter := center3087
  contactBall := contact3087
  work := work3087
  center_sq := center_sq3087
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3087.1
  jac_ok := checks3087.2.1
  accepted := checks3087.2.2

def cells : List CellCertificate := [cell3080, cell3081, cell3082, cell3083, cell3084, cell3085, cell3086, cell3087]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0385


