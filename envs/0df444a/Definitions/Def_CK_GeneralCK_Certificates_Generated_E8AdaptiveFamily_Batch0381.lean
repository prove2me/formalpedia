-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0381
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0381
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:13:48.073831+00:00
-- url     : https://prove2.me/theorems/87f0af3c-9317-44f7-81e0-4c513e41b82c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0381.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0381_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3054 : RatBall :=
  ⟨⟨71/640, -49/128⟩, 3/1280⟩
def center3054 : GaussianRat :=
  ⟨44958767/500000000, -275574013/1000000000⟩
def contact3054 : RatBall := localContactBall tau3054 center3054
def work3054 : RoundedTauEval :=
  evalTau precision tau3054 contact3054 logTwoBall

theorem center_sq3054 : (center3054.re : ℝ)^2 +
    (center3054.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3054]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3054 : work3054.theta.ok = true ∧
    work3054.jac.invOK = true ∧ acceptsUnitSq work3054.out = true := by decide +kernel

def cell3054 : CellCertificate where
  tauBall := tau3054
  contactCenter := center3054
  contactBall := contact3054
  work := work3054
  center_sq := center_sq3054
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3054.1
  jac_ok := checks3054.2.1
  accepted := checks3054.2.2

def tau3055 : RatBall :=
  ⟨⟨13/128, -243/640⟩, 3/1280⟩
def center3055 : GaussianRat :=
  ⟨82196967/1000000000, -136904929/500000000⟩
def contact3055 : RatBall := localContactBall tau3055 center3055
def work3055 : RoundedTauEval :=
  evalTau precision tau3055 contact3055 logTwoBall

theorem center_sq3055 : (center3055.re : ℝ)^2 +
    (center3055.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3055]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3055 : work3055.theta.ok = true ∧
    work3055.jac.invOK = true ∧ acceptsUnitSq work3055.out = true := by decide +kernel

def cell3055 : CellCertificate where
  tauBall := tau3055
  contactCenter := center3055
  contactBall := contact3055
  work := work3055
  center_sq := center_sq3055
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3055.1
  jac_ok := checks3055.2.1
  accepted := checks3055.2.2

def cells : List CellCertificate := [cell3048, cell3049, cell3050, cell3051, cell3052, cell3053, cell3054, cell3055]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381


