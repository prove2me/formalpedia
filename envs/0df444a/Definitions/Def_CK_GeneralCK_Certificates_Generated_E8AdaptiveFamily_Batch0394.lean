-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0394
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0394
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:34:43.150339+00:00
-- url     : https://prove2.me/theorems/1440eda9-cd87-478f-91e3-a0e961eb291d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0394.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0394_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3156 : work3156.theta.ok = true ∧
    work3156.jac.invOK = true ∧ acceptsUnitSq work3156.out = true := by decide +kernel

def cell3156 : CellCertificate where
  tauBall := tau3156
  contactCenter := center3156
  contactBall := contact3156
  work := work3156
  center_sq := center_sq3156
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3156.1
  jac_ok := checks3156.2.1
  accepted := checks3156.2.2

def tau3157 : RatBall :=
  ⟨⟨107/640, -229/640⟩, 3/1280⟩
def center3157 : GaussianRat :=
  ⟨65670547/500000000, -62705679/250000000⟩
def contact3157 : RatBall := localContactBall tau3157 center3157
def work3157 : RoundedTauEval :=
  evalTau precision tau3157 contact3157 logTwoBall

theorem center_sq3157 : (center3157.re : ℝ)^2 +
    (center3157.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3157]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3157 : work3157.theta.ok = true ∧
    work3157.jac.invOK = true ∧ acceptsUnitSq work3157.out = true := by decide +kernel

def cell3157 : CellCertificate where
  tauBall := tau3157
  contactCenter := center3157
  contactBall := contact3157
  work := work3157
  center_sq := center_sq3157
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3157.1
  jac_ok := checks3157.2.1
  accepted := checks3157.2.2

def tau3158 : RatBall :=
  ⟨⟨109/640, -231/640⟩, 3/1280⟩
def center3158 : GaussianRat :=
  ⟨134046881/1000000000, -15803901/62500000⟩
def contact3158 : RatBall := localContactBall tau3158 center3158
def work3158 : RoundedTauEval :=
  evalTau precision tau3158 contact3158 logTwoBall

theorem center_sq3158 : (center3158.re : ℝ)^2 +
    (center3158.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3158]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3158 : work3158.theta.ok = true ∧
    work3158.jac.invOK = true ∧ acceptsUnitSq work3158.out = true := by decide +kernel

def cell3158 : CellCertificate where
  tauBall := tau3158
  contactCenter := center3158
  contactBall := contact3158
  work := work3158
  center_sq := center_sq3158
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3158.1
  jac_ok := checks3158.2.1
  accepted := checks3158.2.2

def tau3159 : RatBall :=
  ⟨⟨111/640, -231/640⟩, 3/1280⟩
def center3159 : GaussianRat :=
  ⟨34104423/250000000, -25252199/100000000⟩
def contact3159 : RatBall := localContactBall tau3159 center3159
def work3159 : RoundedTauEval :=
  evalTau precision tau3159 contact3159 logTwoBall

theorem center_sq3159 : (center3159.re : ℝ)^2 +
    (center3159.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3159]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3159 : work3159.theta.ok = true ∧
    work3159.jac.invOK = true ∧ acceptsUnitSq work3159.out = true := by decide +kernel

def cell3159 : CellCertificate where
  tauBall := tau3159
  contactCenter := center3159
  contactBall := contact3159
  work := work3159
  center_sq := center_sq3159
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3159.1
  jac_ok := checks3159.2.1
  accepted := checks3159.2.2

def cells : List CellCertificate := [cell3152, cell3153, cell3154, cell3155, cell3156, cell3157, cell3158, cell3159]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394


