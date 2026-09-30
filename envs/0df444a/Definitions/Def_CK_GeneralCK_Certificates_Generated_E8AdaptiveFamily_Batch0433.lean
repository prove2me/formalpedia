-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0433
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0433
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:28:57.899583+00:00
-- url     : https://prove2.me/theorems/6a56c350-71e4-4916-81f8-876dbdb0cac6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0433.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0433_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3470 : RatBall :=
  ⟨⟨-31/640, 51/128⟩, 3/1280⟩
def center3470 : GaussianRat :=
  ⟨-20060649/500000000, 146045357/500000000⟩
def contact3470 : RatBall := localContactBall tau3470 center3470
def work3470 : RoundedTauEval :=
  evalTau precision tau3470 contact3470 logTwoBall

theorem center_sq3470 : (center3470.re : ℝ)^2 +
    (center3470.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3470]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3470 : work3470.theta.ok = true ∧
    work3470.jac.invOK = true ∧ acceptsUnitSq work3470.out = true := by decide +kernel

def cell3470 : CellCertificate where
  tauBall := tau3470
  contactCenter := center3470
  contactBall := contact3470
  work := work3470
  center_sq := center_sq3470
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3470.1
  jac_ok := checks3470.2.1
  accepted := checks3470.2.2

def tau3471 : RatBall :=
  ⟨⟨-29/640, 51/128⟩, 3/1280⟩
def center3471 : GaussianRat :=
  ⟨-2346303/62500000, 292209741/1000000000⟩
def contact3471 : RatBall := localContactBall tau3471 center3471
def work3471 : RoundedTauEval :=
  evalTau precision tau3471 contact3471 logTwoBall

theorem center_sq3471 : (center3471.re : ℝ)^2 +
    (center3471.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3471]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3471 : work3471.theta.ok = true ∧
    work3471.jac.invOK = true ∧ acceptsUnitSq work3471.out = true := by decide +kernel

def cell3471 : CellCertificate where
  tauBall := tau3471
  contactCenter := center3471
  contactBall := contact3471
  work := work3471
  center_sq := center_sq3471
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3471.1
  jac_ok := checks3471.2.1
  accepted := checks3471.2.2

def cells : List CellCertificate := [cell3464, cell3465, cell3466, cell3467, cell3468, cell3469, cell3470, cell3471]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433


