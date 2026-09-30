-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0479
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0479
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:31:29.732522+00:00
-- url     : https://prove2.me/theorems/d36c40a8-a6e5-4fa7-a77f-c75592b1ed5d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0479` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0479` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0479` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0479 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0479.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0479_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0479

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3838 : (center3838.re : ℝ)^2 +
    (center3838.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3838]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3838 : work3838.theta.ok = true ∧
    work3838.jac.invOK = true ∧ acceptsUnitSq work3838.out = true := by decide +kernel

def cell3838 : CellCertificate where
  tauBall := tau3838
  contactCenter := center3838
  contactBall := contact3838
  work := work3838
  center_sq := center_sq3838
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3838.1
  jac_ok := checks3838.2.1
  accepted := checks3838.2.2

def tau3839 : RatBall :=
  ⟨⟨27/128, 219/640⟩, 3/1280⟩
def center3839 : GaussianRat :=
  ⟨162184187/1000000000, 234275597/1000000000⟩
def contact3839 : RatBall := localContactBall tau3839 center3839
def work3839 : RoundedTauEval :=
  evalTau precision tau3839 contact3839 logTwoBall

theorem center_sq3839 : (center3839.re : ℝ)^2 +
    (center3839.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3839]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3839 : work3839.theta.ok = true ∧
    work3839.jac.invOK = true ∧ acceptsUnitSq work3839.out = true := by decide +kernel

def cell3839 : CellCertificate where
  tauBall := tau3839
  contactCenter := center3839
  contactBall := contact3839
  work := work3839
  center_sq := center_sq3839
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3839.1
  jac_ok := checks3839.2.1
  accepted := checks3839.2.2

def cells : List CellCertificate := [cell3832, cell3833, cell3834, cell3835, cell3836, cell3837, cell3838, cell3839]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0479


