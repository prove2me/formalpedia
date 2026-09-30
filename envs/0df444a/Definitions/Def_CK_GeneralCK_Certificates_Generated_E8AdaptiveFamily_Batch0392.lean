-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0392
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0392
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:42:09.207369+00:00
-- url     : https://prove2.me/theorems/e6315205-dc67-46ab-aadc-264a633d7a99
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0392` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0392` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0392` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0392 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0392.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0392_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0392

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center3142 : GaussianRat :=
  ⟨1987999/15625000, -12812079/50000000⟩
def contact3142 : RatBall := localContactBall tau3142 center3142
def work3142 : RoundedTauEval :=
  evalTau precision tau3142 contact3142 logTwoBall

theorem center_sq3142 : (center3142.re : ℝ)^2 +
    (center3142.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3142]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3142 : work3142.theta.ok = true ∧
    work3142.jac.invOK = true ∧ acceptsUnitSq work3142.out = true := by decide +kernel

def cell3142 : CellCertificate where
  tauBall := tau3142
  contactCenter := center3142
  contactBall := contact3142
  work := work3142
  center_sq := center_sq3142
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3142.1
  jac_ok := checks3142.2.1
  accepted := checks3142.2.2

def tau3143 : RatBall :=
  ⟨⟨21/128, -233/640⟩, 3/1280⟩
def center3143 : GaussianRat :=
  ⟨8101339/62500000, -3998631/15625000⟩
def contact3143 : RatBall := localContactBall tau3143 center3143
def work3143 : RoundedTauEval :=
  evalTau precision tau3143 contact3143 logTwoBall

theorem center_sq3143 : (center3143.re : ℝ)^2 +
    (center3143.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3143]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3143 : work3143.theta.ok = true ∧
    work3143.jac.invOK = true ∧ acceptsUnitSq work3143.out = true := by decide +kernel

def cell3143 : CellCertificate where
  tauBall := tau3143
  contactCenter := center3143
  contactBall := contact3143
  work := work3143
  center_sq := center_sq3143
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3143.1
  jac_ok := checks3143.2.1
  accepted := checks3143.2.2

def cells : List CellCertificate := [cell3136, cell3137, cell3138, cell3139, cell3140, cell3141, cell3142, cell3143]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0392


