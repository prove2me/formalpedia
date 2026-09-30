-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0450
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0450
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:24:12.80274+00:00
-- url     : https://prove2.me/theorems/d56546a5-1782-47fa-94b9-636943a2fe90
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0450` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0450` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0450` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0450 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0450.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0450_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0450

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3606 : RoundedTauEval :=
  evalTau precision tau3606 contact3606 logTwoBall

theorem center_sq3606 : (center3606.re : ℝ)^2 +
    (center3606.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3606]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3606 : work3606.theta.ok = true ∧
    work3606.jac.invOK = true ∧ acceptsUnitSq work3606.out = true := by decide +kernel

def cell3606 : CellCertificate where
  tauBall := tau3606
  contactCenter := center3606
  contactBall := contact3606
  work := work3606
  center_sq := center_sq3606
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3606.1
  jac_ok := checks3606.2.1
  accepted := checks3606.2.2

def tau3607 : RatBall :=
  ⟨⟨39/640, 247/640⟩, 3/1280⟩
def center3607 : GaussianRat :=
  ⟨49825917/1000000000, 281309513/1000000000⟩
def contact3607 : RatBall := localContactBall tau3607 center3607
def work3607 : RoundedTauEval :=
  evalTau precision tau3607 contact3607 logTwoBall

theorem center_sq3607 : (center3607.re : ℝ)^2 +
    (center3607.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3607]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3607 : work3607.theta.ok = true ∧
    work3607.jac.invOK = true ∧ acceptsUnitSq work3607.out = true := by decide +kernel

def cell3607 : CellCertificate where
  tauBall := tau3607
  contactCenter := center3607
  contactBall := contact3607
  work := work3607
  center_sq := center_sq3607
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3607.1
  jac_ok := checks3607.2.1
  accepted := checks3607.2.2

def cells : List CellCertificate := [cell3600, cell3601, cell3602, cell3603, cell3604, cell3605, cell3606, cell3607]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0450


