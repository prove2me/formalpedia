-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0459
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0459
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:48:39.683474+00:00
-- url     : https://prove2.me/theorems/4467069a-9a3d-45b8-8dc3-47269c27a144
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0459` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0459` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0459` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0459 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0459.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0459_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0459

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3678 : (center3678.re : ℝ)^2 +
    (center3678.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3678]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3678 : work3678.theta.ok = true ∧
    work3678.jac.invOK = true ∧ acceptsUnitSq work3678.out = true := by decide +kernel

def cell3678 : CellCertificate where
  tauBall := tau3678
  contactCenter := center3678
  contactBall := contact3678
  work := work3678
  center_sq := center_sq3678
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3678.1
  jac_ok := checks3678.2.1
  accepted := checks3678.2.2

def tau3679 : RatBall :=
  ⟨⟨53/640, 249/640⟩, 3/1280⟩
def center3679 : GaussianRat :=
  ⟨33881037/500000000, 282642041/1000000000⟩
def contact3679 : RatBall := localContactBall tau3679 center3679
def work3679 : RoundedTauEval :=
  evalTau precision tau3679 contact3679 logTwoBall

theorem center_sq3679 : (center3679.re : ℝ)^2 +
    (center3679.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3679]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3679 : work3679.theta.ok = true ∧
    work3679.jac.invOK = true ∧ acceptsUnitSq work3679.out = true := by decide +kernel

def cell3679 : CellCertificate where
  tauBall := tau3679
  contactCenter := center3679
  contactBall := contact3679
  work := work3679
  center_sq := center_sq3679
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3679.1
  jac_ok := checks3679.2.1
  accepted := checks3679.2.2

def cells : List CellCertificate := [cell3672, cell3673, cell3674, cell3675, cell3676, cell3677, cell3678, cell3679]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0459


