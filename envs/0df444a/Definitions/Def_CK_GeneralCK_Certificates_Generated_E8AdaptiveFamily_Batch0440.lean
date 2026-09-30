-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0440
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0440
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:08:24.239466+00:00
-- url     : https://prove2.me/theorems/d063be2b-6093-4dae-a6a5-a8000f614cdb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0440.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0440_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell3525 : CellCertificate where
  tauBall := tau3525
  contactCenter := center3525
  contactBall := contact3525
  work := work3525
  center_sq := center_sq3525
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3525.1
  jac_ok := checks3525.2.1
  accepted := checks3525.2.2

def tau3526 : RatBall :=
  ⟨⟨1/640, 251/640⟩, 3/1280⟩
def center3526 : GaussianRat :=
  ⟨1288571/1000000000, 287876293/1000000000⟩
def contact3526 : RatBall := localContactBall tau3526 center3526
def work3526 : RoundedTauEval :=
  evalTau precision tau3526 contact3526 logTwoBall

theorem center_sq3526 : (center3526.re : ℝ)^2 +
    (center3526.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3526]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3526 : work3526.theta.ok = true ∧
    work3526.jac.invOK = true ∧ acceptsUnitSq work3526.out = true := by decide +kernel

def cell3526 : CellCertificate where
  tauBall := tau3526
  contactCenter := center3526
  contactBall := contact3526
  work := work3526
  center_sq := center_sq3526
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3526.1
  jac_ok := checks3526.2.1
  accepted := checks3526.2.2

def tau3527 : RatBall :=
  ⟨⟨3/640, 251/640⟩, 3/1280⟩
def center3527 : GaussianRat :=
  ⟨193283/50000000, 143934259/500000000⟩
def contact3527 : RatBall := localContactBall tau3527 center3527
def work3527 : RoundedTauEval :=
  evalTau precision tau3527 contact3527 logTwoBall

theorem center_sq3527 : (center3527.re : ℝ)^2 +
    (center3527.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3527]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3527 : work3527.theta.ok = true ∧
    work3527.jac.invOK = true ∧ acceptsUnitSq work3527.out = true := by decide +kernel

def cell3527 : CellCertificate where
  tauBall := tau3527
  contactCenter := center3527
  contactBall := contact3527
  work := work3527
  center_sq := center_sq3527
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3527.1
  jac_ok := checks3527.2.1
  accepted := checks3527.2.2

def cells : List CellCertificate := [cell3520, cell3521, cell3522, cell3523, cell3524, cell3525, cell3526, cell3527]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440


