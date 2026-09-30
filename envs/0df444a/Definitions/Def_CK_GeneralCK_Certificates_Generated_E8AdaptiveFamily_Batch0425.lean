-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0425
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0425
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:31:22.904887+00:00
-- url     : https://prove2.me/theorems/ac23ce90-260b-492b-a2a4-ba5ddd667a1f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0425` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0425` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0425` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0425 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0425.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0425_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0425

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3406 : RoundedTauEval :=
  evalTau precision tau3406 contact3406 logTwoBall

theorem center_sq3406 : (center3406.re : ℝ)^2 +
    (center3406.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3406]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3406 : work3406.theta.ok = true ∧
    work3406.jac.invOK = true ∧ acceptsUnitSq work3406.out = true := by decide +kernel

def cell3406 : CellCertificate where
  tauBall := tau3406
  contactCenter := center3406
  contactBall := contact3406
  work := work3406
  center_sq := center_sq3406
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3406.1
  jac_ok := checks3406.2.1
  accepted := checks3406.2.2

def tau3407 : RatBall :=
  ⟨⟨-47/640, 243/640⟩, 3/1280⟩
def center3407 : GaussianRat :=
  ⟨-59632267/1000000000, 137808407/500000000⟩
def contact3407 : RatBall := localContactBall tau3407 center3407
def work3407 : RoundedTauEval :=
  evalTau precision tau3407 contact3407 logTwoBall

theorem center_sq3407 : (center3407.re : ℝ)^2 +
    (center3407.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3407]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3407 : work3407.theta.ok = true ∧
    work3407.jac.invOK = true ∧ acceptsUnitSq work3407.out = true := by decide +kernel

def cell3407 : CellCertificate where
  tauBall := tau3407
  contactCenter := center3407
  contactBall := contact3407
  work := work3407
  center_sq := center_sq3407
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3407.1
  jac_ok := checks3407.2.1
  accepted := checks3407.2.2

def cells : List CellCertificate := [cell3400, cell3401, cell3402, cell3403, cell3404, cell3405, cell3406, cell3407]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0425


