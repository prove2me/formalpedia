-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0447_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0447_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:14:43.614283+00:00
-- url     : https://prove2.me/theorems/211133ec-57e4-4d3d-9bf9-80bd45a0bc76
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0447 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0447_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3578 : (center3578.re : ℝ)^2 +
    (center3578.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3578]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3578 : work3578.theta.ok = true ∧
    work3578.jac.invOK = true ∧ acceptsUnitSq work3578.out = true := by decide +kernel

def cell3578 : CellCertificate where
  tauBall := tau3578
  contactCenter := center3578
  contactBall := contact3578
  work := work3578
  center_sq := center_sq3578
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3578.1
  jac_ok := checks3578.2.1
  accepted := checks3578.2.2

def tau3579 : RatBall :=
  ⟨⟨19/640, 51/128⟩, 3/1280⟩
def center3579 : GaussianRat :=
  ⟨24616799/1000000000, 73171759/250000000⟩
def contact3579 : RatBall := localContactBall tau3579 center3579
def work3579 : RoundedTauEval :=
  evalTau precision tau3579 contact3579 logTwoBall

theorem center_sq3579 : (center3579.re : ℝ)^2 +
    (center3579.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3579]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3579 : work3579.theta.ok = true ∧
    work3579.jac.invOK = true ∧ acceptsUnitSq work3579.out = true := by decide +kernel

def cell3579 : CellCertificate where
  tauBall := tau3579
  contactCenter := center3579
  contactBall := contact3579
  work := work3579
  center_sq := center_sq3579
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3579.1
  jac_ok := checks3579.2.1
  accepted := checks3579.2.2

def tau3580 : RatBall :=
  ⟨⟨21/640, 253/640⟩, 3/1280⟩
def center3580 : GaussianRat :=
  ⟨5424219/200000000, 290024499/1000000000⟩
def contact3580 : RatBall := localContactBall tau3580 center3580
def work3580 : RoundedTauEval :=
  evalTau precision tau3580 contact3580 logTwoBall

theorem center_sq3580 : (center3580.re : ℝ)^2 +
    (center3580.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3580]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3580 : work3580.theta.ok = true ∧
    work3580.jac.invOK = true ∧ acceptsUnitSq work3580.out = true := by decide +kernel

def cell3580 : CellCertificate where
  tauBall := tau3580
  contactCenter := center3580
  contactBall := contact3580
  work := work3580
  center_sq := center_sq3580
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3580.1
  jac_ok := checks3580.2.1
  accepted := checks3580.2.2

def tau3581 : RatBall :=
  ⟨⟨23/640, 253/640⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447


