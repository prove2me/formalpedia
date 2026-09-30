-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0474
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0474
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:49:54.606692+00:00
-- url     : https://prove2.me/theorems/43b28174-949a-43bd-8c5c-e6bdf8c5c131
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0474` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0474` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0474` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0474 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0474.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0474_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0474

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3798 : RoundedTauEval :=
  evalTau precision tau3798 contact3798 logTwoBall

theorem center_sq3798 : (center3798.re : ℝ)^2 +
    (center3798.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3798]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3798 : work3798.theta.ok = true ∧
    work3798.jac.invOK = true ∧ acceptsUnitSq work3798.out = true := by decide +kernel

def cell3798 : CellCertificate where
  tauBall := tau3798
  contactCenter := center3798
  contactBall := contact3798
  work := work3798
  center_sq := center_sq3798
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3798.1
  jac_ok := checks3798.2.1
  accepted := checks3798.2.2

def tau3799 : RatBall :=
  ⟨⟨109/640, 231/640⟩, 3/1280⟩
def center3799 : GaussianRat :=
  ⟨134046881/1000000000, 15803901/62500000⟩
def contact3799 : RatBall := localContactBall tau3799 center3799
def work3799 : RoundedTauEval :=
  evalTau precision tau3799 contact3799 logTwoBall

theorem center_sq3799 : (center3799.re : ℝ)^2 +
    (center3799.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3799]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3799 : work3799.theta.ok = true ∧
    work3799.jac.invOK = true ∧ acceptsUnitSq work3799.out = true := by decide +kernel

def cell3799 : CellCertificate where
  tauBall := tau3799
  contactCenter := center3799
  contactBall := contact3799
  work := work3799
  center_sq := center_sq3799
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3799.1
  jac_ok := checks3799.2.1
  accepted := checks3799.2.2

def cells : List CellCertificate := [cell3792, cell3793, cell3794, cell3795, cell3796, cell3797, cell3798, cell3799]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0474


