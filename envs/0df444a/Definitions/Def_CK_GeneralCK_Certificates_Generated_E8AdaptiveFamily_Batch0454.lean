-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0454
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0454
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:05:31.183809+00:00
-- url     : https://prove2.me/theorems/1de56c5e-7a3d-4a32-9227-a351bc011f71
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0454` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0454` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0454` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0454 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0454.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0454_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0454

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact3638 : RatBall := localContactBall tau3638 center3638
def work3638 : RoundedTauEval :=
  evalTau precision tau3638 contact3638 logTwoBall

theorem center_sq3638 : (center3638.re : ℝ)^2 +
    (center3638.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3638]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3638 : work3638.theta.ok = true ∧
    work3638.jac.invOK = true ∧ acceptsUnitSq work3638.out = true := by decide +kernel

def cell3638 : CellCertificate where
  tauBall := tau3638
  contactCenter := center3638
  contactBall := contact3638
  work := work3638
  center_sq := center_sq3638
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3638.1
  jac_ok := checks3638.2.1
  accepted := checks3638.2.2

def tau3639 : RatBall :=
  ⟨⟨47/640, 251/640⟩, 3/1280⟩
def center3639 : GaussianRat :=
  ⟨1508267/25000000, 71437399/250000000⟩
def contact3639 : RatBall := localContactBall tau3639 center3639
def work3639 : RoundedTauEval :=
  evalTau precision tau3639 contact3639 logTwoBall

theorem center_sq3639 : (center3639.re : ℝ)^2 +
    (center3639.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3639]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3639 : work3639.theta.ok = true ∧
    work3639.jac.invOK = true ∧ acceptsUnitSq work3639.out = true := by decide +kernel

def cell3639 : CellCertificate where
  tauBall := tau3639
  contactCenter := center3639
  contactBall := contact3639
  work := work3639
  center_sq := center_sq3639
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3639.1
  jac_ok := checks3639.2.1
  accepted := checks3639.2.2

def cells : List CellCertificate := [cell3632, cell3633, cell3634, cell3635, cell3636, cell3637, cell3638, cell3639]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0454


