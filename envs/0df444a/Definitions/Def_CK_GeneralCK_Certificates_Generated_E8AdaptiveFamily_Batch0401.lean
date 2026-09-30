-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0401
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0401
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:04:41.899761+00:00
-- url     : https://prove2.me/theorems/e7da38e3-69ac-4f5d-a5c2-4232bb02120f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0401` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0401` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0401` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0401 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0401.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0401 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0401

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3208 : RatBall :=
  ⟨⟨-137/640, 217/640⟩, 3/1280⟩
def center3208 : GaussianRat :=
  ⟨-41023473/250000000, 231626927/1000000000⟩
def contact3208 : RatBall := localContactBall tau3208 center3208
def work3208 : RoundedTauEval :=
  evalTau precision tau3208 contact3208 logTwoBall

theorem center_sq3208 : (center3208.re : ℝ)^2 +
    (center3208.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3208]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3208 : work3208.theta.ok = true ∧
    work3208.jac.invOK = true ∧ acceptsUnitSq work3208.out = true := by decide +kernel

def cell3208 : CellCertificate where
  tauBall := tau3208
  contactCenter := center3208
  contactBall := contact3208
  work := work3208
  center_sq := center_sq3208
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3208.1
  jac_ok := checks3208.2.1
  accepted := checks3208.2.2

def tau3209 : RatBall :=
  ⟨⟨-27/128, 217/640⟩, 3/1280⟩
def center3209 : GaussianRat :=
  ⟨-80908379/500000000, 115996981/500000000⟩
def contact3209 : RatBall := localContactBall tau3209 center3209
def work3209 : RoundedTauEval :=
  evalTau precision tau3209 contact3209 logTwoBall

theorem center_sq3209 : (center3209.re : ℝ)^2 +
    (center3209.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3209]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3209 : work3209.theta.ok = true ∧
    work3209.jac.invOK = true ∧ acceptsUnitSq work3209.out = true := by decide +kernel

def cell3209 : CellCertificate where
  tauBall := tau3209
  contactCenter := center3209
  contactBall := contact3209
  work := work3209
  center_sq := center_sq3209
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3209.1
  jac_ok := checks3209.2.1
  accepted := checks3209.2.2

def tau3210 : RatBall :=
  ⟨⟨-133/640, 217/640⟩, 3/1280⟩
def center3210 : GaussianRat :=
  ⟨-79767381/500000000, 29044611/125000000⟩
def contact3210 : RatBall := localContactBall tau3210 center3210
def work3210 : RoundedTauEval :=
  evalTau precision tau3210 contact3210 logTwoBall

theorem center_sq3210 : (center3210.re : ℝ)^2 +
    (center3210.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3210]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3210 : work3210.theta.ok = true ∧
    work3210.jac.invOK = true ∧ acceptsUnitSq work3210.out = true := by decide +kernel

def cell3210 : CellCertificate where
  tauBall := tau3210
  contactCenter := center3210
  contactBall := contact3210
  work := work3210
  center_sq := center_sq3210
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3210.1
  jac_ok := checks3210.2.1
  accepted := checks3210.2.2

def tau3211 : RatBall :=
  ⟨⟨-27/128, 219/640⟩, 3/1280⟩
def center3211 : GaussianRat :=
  ⟨-162184187/1000000000, 234275597/1000000000⟩
def contact3211 : RatBall := localContactBall tau3211 center3211
def work3211 : RoundedTauEval :=
  evalTau precision tau3211 contact3211 logTwoBall

theorem center_sq3211 : (center3211.re : ℝ)^2 +
    (center3211.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3211]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3211 : work3211.theta.ok = true ∧
    work3211.jac.invOK = true ∧ acceptsUnitSq work3211.out = true := by decide +kernel

def cell3211 : CellCertificate where
  tauBall := tau3211
  contactCenter := center3211
  contactBall := contact3211
  work := work3211
  center_sq := center_sq3211
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3211.1
  jac_ok := checks3211.2.1
  accepted := checks3211.2.2

def tau3212 : RatBall :=
  ⟨⟨-133/640, 219/640⟩, 3/1280⟩
def center3212 : GaussianRat :=
  ⟨-159898033/1000000000, 234643387/1000000000⟩
def contact3212 : RatBall := localContactBall tau3212 center3212
def work3212 : RoundedTauEval :=
  evalTau precision tau3212 contact3212 logTwoBall

theorem center_sq3212 : (center3212.re : ℝ)^2 +
    (center3212.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3212]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3212 : work3212.theta.ok = true ∧
    work3212.jac.invOK = true ∧ acceptsUnitSq work3212.out = true := by decide +kernel

def cell3212 : CellCertificate where
  tauBall := tau3212
  contactCenter := center3212
  contactBall := contact3212
  work := work3212
  center_sq := center_sq3212
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3212.1
  jac_ok := checks3212.2.1
  accepted := checks3212.2.2

def tau3213 : RatBall :=
  ⟨⟨-131/640, 217/640⟩, 3/1280⟩
def center3213 : GaussianRat :=
  ⟨-157247951/1000000000, 46543131/200000000⟩
def contact3213 : RatBall := localContactBall tau3213 center3213
def work3213 : RoundedTauEval :=
  evalTau precision tau3213 contact3213 logTwoBall

theorem center_sq3213 : (center3213.re : ℝ)^2 +
    (center3213.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3213]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3213 : work3213.theta.ok = true ∧
    work3213.jac.invOK = true ∧ acceptsUnitSq work3213.out = true := by decide +kernel

def cell3213 : CellCertificate where
  tauBall := tau3213
  contactCenter := center3213
  contactBall := contact3213
  work := work3213
  center_sq := center_sq3213
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3213.1
  jac_ok := checks3213.2.1
  accepted := checks3213.2.2

def tau3214 : RatBall :=
  ⟨⟨-129/640, 217/640⟩, 3/1280⟩
def center3214 : GaussianRat :=
  ⟨-38739093/250000000, 233070213/1000000000⟩
def contact3214 : RatBall := localContactBall tau3214 center3214
def work3214 : RoundedTauEval :=
  evalTau precision tau3214 contact3214 logTwoBall

theorem center_sq3214 : (center3214.re : ℝ)^2 +
    (center3214.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3214]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3214 : work3214.theta.ok = true ∧
    work3214.jac.invOK = true ∧ acceptsUnitSq work3214.out = true := by decide +kernel

def cell3214 : CellCertificate where
  tauBall := tau3214
  contactCenter := center3214
  contactBall := contact3214
  work := work3214
  center_sq := center_sq3214
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3214.1
  jac_ok := checks3214.2.1
  accepted := checks3214.2.2

def tau3215 : RatBall :=
  ⟨⟨-131/640, 219/640⟩, 3/1280⟩
def center3215 : GaussianRat :=
  ⟨-157607013/1000000000, 23500697/100000000⟩
def contact3215 : RatBall := localContactBall tau3215 center3215
def work3215 : RoundedTauEval :=
  evalTau precision tau3215 contact3215 logTwoBall

theorem center_sq3215 : (center3215.re : ℝ)^2 +
    (center3215.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3215]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3215 : work3215.theta.ok = true ∧
    work3215.jac.invOK = true ∧ acceptsUnitSq work3215.out = true := by decide +kernel

def cell3215 : CellCertificate where
  tauBall := tau3215
  contactCenter := center3215
  contactBall := contact3215
  work := work3215
  center_sq := center_sq3215
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3215.1
  jac_ok := checks3215.2.1
  accepted := checks3215.2.2

def cells : List CellCertificate := [cell3208, cell3209, cell3210, cell3211, cell3212, cell3213, cell3214, cell3215]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0401

end


