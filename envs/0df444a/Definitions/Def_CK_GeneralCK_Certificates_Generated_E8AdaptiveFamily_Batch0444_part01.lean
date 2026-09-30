-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0444_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0444_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:48:56.251566+00:00
-- url     : https://prove2.me/theorems/21c7f6be-b4d2-464d-84c3-3acc63a368a0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0444 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0444_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3555 : (center3555.re : ℝ)^2 +
    (center3555.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3555]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3555 : work3555.theta.ok = true ∧
    work3555.jac.invOK = true ∧ acceptsUnitSq work3555.out = true := by decide +kernel

def cell3555 : CellCertificate where
  tauBall := tau3555
  contactCenter := center3555
  contactBall := contact3555
  work := work3555
  center_sq := center_sq3555
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3555.1
  jac_ok := checks3555.2.1
  accepted := checks3555.2.2

def tau3556 : RatBall :=
  ⟨⟨21/640, 49/128⟩, 3/1280⟩
def center3556 : GaussianRat :=
  ⟨6700043/250000000, 139884999/500000000⟩
def contact3556 : RatBall := localContactBall tau3556 center3556
def work3556 : RoundedTauEval :=
  evalTau precision tau3556 contact3556 logTwoBall

theorem center_sq3556 : (center3556.re : ℝ)^2 +
    (center3556.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3556]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3556 : work3556.theta.ok = true ∧
    work3556.jac.invOK = true ∧ acceptsUnitSq work3556.out = true := by decide +kernel

def cell3556 : CellCertificate where
  tauBall := tau3556
  contactCenter := center3556
  contactBall := contact3556
  work := work3556
  center_sq := center_sq3556
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3556.1
  jac_ok := checks3556.2.1
  accepted := checks3556.2.2

def tau3557 : RatBall :=
  ⟨⟨23/640, 49/128⟩, 3/1280⟩
def center3557 : GaussianRat :=
  ⟨7337051/250000000, 279688291/1000000000⟩
def contact3557 : RatBall := localContactBall tau3557 center3557
def work3557 : RoundedTauEval :=
  evalTau precision tau3557 contact3557 logTwoBall

theorem center_sq3557 : (center3557.re : ℝ)^2 +
    (center3557.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3557]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3557 : work3557.theta.ok = true ∧
    work3557.jac.invOK = true ∧ acceptsUnitSq work3557.out = true := by decide +kernel

def cell3557 : CellCertificate where
  tauBall := tau3557
  contactCenter := center3557
  contactBall := contact3557
  work := work3557
  center_sq := center_sq3557
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3557.1
  jac_ok := checks3557.2.1
  accepted := checks3557.2.2

def tau3558 : RatBall :=
  ⟨⟨21/640, 247/640⟩, 3/1280⟩
def center3558 : GaussianRat :=
  ⟨26878737/1000000000, 282322297/1000000000⟩
def contact3558 : RatBall := localContactBall tau3558 center3558
def work3558 : RoundedTauEval :=
  evalTau precision tau3558 contact3558 logTwoBall

theorem center_sq3558 : (center3558.re : ℝ)^2 +
    (center3558.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3558]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3558 : work3558.theta.ok = true ∧
    work3558.jac.invOK = true ∧ acceptsUnitSq work3558.out = true := by decide +kernel

def cell3558 : CellCertificate where
  tauBall := tau3558
  contactCenter := center3558
  contactBall := contact3558
  work := work3558
  center_sq := center_sq3558
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3558.1
  jac_ok := checks3558.2.1
  accepted := checks3558.2.2

def tau3559 : RatBall :=
  ⟨⟨23/640, 247/640⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444


