-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0424
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0424
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:45:39.388591+00:00
-- url     : https://prove2.me/theorems/6b31e401-834a-4bb1-8669-6fba568f7a32
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0424.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0424_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3398 : (center3398.re : ℝ)^2 +
    (center3398.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3398]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3398 : work3398.theta.ok = true ∧
    work3398.jac.invOK = true ∧ acceptsUnitSq work3398.out = true := by decide +kernel

def cell3398 : CellCertificate where
  tauBall := tau3398
  contactCenter := center3398
  contactBall := contact3398
  work := work3398
  center_sq := center_sq3398
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3398.1
  jac_ok := checks3398.2.1
  accepted := checks3398.2.2

def tau3399 : RatBall :=
  ⟨⟨-11/128, 251/640⟩, 3/1280⟩
def center3399 : GaussianRat :=
  ⟨-70500491/1000000000, 35621651/125000000⟩
def contact3399 : RatBall := localContactBall tau3399 center3399
def work3399 : RoundedTauEval :=
  evalTau precision tau3399 contact3399 logTwoBall

theorem center_sq3399 : (center3399.re : ℝ)^2 +
    (center3399.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3399]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3399 : work3399.theta.ok = true ∧
    work3399.jac.invOK = true ∧ acceptsUnitSq work3399.out = true := by decide +kernel

def cell3399 : CellCertificate where
  tauBall := tau3399
  contactCenter := center3399
  contactBall := contact3399
  work := work3399
  center_sq := center_sq3399
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3399.1
  jac_ok := checks3399.2.1
  accepted := checks3399.2.2

def cells : List CellCertificate := [cell3392, cell3393, cell3394, cell3395, cell3396, cell3397, cell3398, cell3399]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424


