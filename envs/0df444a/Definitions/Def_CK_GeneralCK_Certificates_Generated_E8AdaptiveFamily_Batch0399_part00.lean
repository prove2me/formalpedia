-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0399_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0399_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:27:38.978657+00:00
-- url     : https://prove2.me/theorems/d2e3419b-8231-486d-9024-023a735474d2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0399 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0399 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0399 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0399 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0399 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0399

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3192 : RatBall :=
  ⟨⟨131/640, -219/640⟩, 3/1280⟩
def center3192 : GaussianRat :=
  ⟨157607013/1000000000, -23500697/100000000⟩
def contact3192 : RatBall := localContactBall tau3192 center3192
def work3192 : RoundedTauEval :=
  evalTau precision tau3192 contact3192 logTwoBall

theorem center_sq3192 : (center3192.re : ℝ)^2 +
    (center3192.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3192 : work3192.theta.ok = true ∧
    work3192.jac.invOK = true ∧ acceptsUnitSq work3192.out = true := by decide +kernel

def cell3192 : CellCertificate where
  tauBall := tau3192
  contactCenter := center3192
  contactBall := contact3192
  work := work3192
  center_sq := center_sq3192
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3192.1
  jac_ok := checks3192.2.1
  accepted := checks3192.2.2

def tau3193 : RatBall :=
  ⟨⟨129/640, -217/640⟩, 3/1280⟩
def center3193 : GaussianRat :=
  ⟨38739093/250000000, -233070213/1000000000⟩
def contact3193 : RatBall := localContactBall tau3193 center3193
def work3193 : RoundedTauEval :=
  evalTau precision tau3193 contact3193 logTwoBall

theorem center_sq3193 : (center3193.re : ℝ)^2 +
    (center3193.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3193]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3193 : work3193.theta.ok = true ∧
    work3193.jac.invOK = true ∧ acceptsUnitSq work3193.out = true := by decide +kernel

def cell3193 : CellCertificate where
  tauBall := tau3193
  contactCenter := center3193
  contactBall := contact3193
  work := work3193
  center_sq := center_sq3193
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3193.1
  jac_ok := checks3193.2.1
  accepted := checks3193.2.2

def tau3194 : RatBall :=
  ⟨⟨131/640, -217/640⟩, 3/1280⟩
def center3194 : GaussianRat :=
  ⟨157247951/1000000000, -46543131/200000000⟩
def contact3194 : RatBall := localContactBall tau3194 center3194
def work3194 : RoundedTauEval :=
  evalTau precision tau3194 contact3194 logTwoBall

theorem center_sq3194 : (center3194.re : ℝ)^2 +
    (center3194.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3194]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3194 : work3194.theta.ok = true ∧
    work3194.jac.invOK = true ∧ acceptsUnitSq work3194.out = true := by decide +kernel

def cell3194 : CellCertificate where
  tauBall := tau3194
  contactCenter := center3194
  contactBall := contact3194
  work := work3194
  center_sq := center_sq3194
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3194.1
  jac_ok := checks3194.2.1
  accepted := checks3194.2.2

def tau3195 : RatBall :=
  ⟨⟨133/640, -219/640⟩, 3/1280⟩
def center3195 : GaussianRat :=
  ⟨159898033/1000000000, -234643387/1000000000⟩
def contact3195 : RatBall := localContactBall tau3195 center3195
def work3195 : RoundedTauEval :=
  evalTau precision tau3195 contact3195 logTwoBall

theorem center_sq3195 : (center3195.re : ℝ)^2 +
    (center3195.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3195]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3195 : work3195.theta.ok = true ∧
    work3195.jac.invOK = true ∧ acceptsUnitSq work3195.out = true := by decide +kernel

def cell3195 : CellCertificate where
  tauBall := tau3195
  contactCenter := center3195
  contactBall := contact3195
  work := work3195
  center_sq := center_sq3195
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3195.1
  jac_ok := checks3195.2.1
  accepted := checks3195.2.2

def tau3196 : RatBall :=
  ⟨⟨27/128, -219/640⟩, 3/1280⟩
def center3196 : GaussianRat :=
  ⟨162184187/1000000000, -234275597/1000000000⟩
def contact3196 : RatBall := localContactBall tau3196 center3196

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0399


