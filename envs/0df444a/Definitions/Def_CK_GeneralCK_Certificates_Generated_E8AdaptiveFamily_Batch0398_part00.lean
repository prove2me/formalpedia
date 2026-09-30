-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0398_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0398_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:12:36.210898+00:00
-- url     : https://prove2.me/theorems/9b6cff03-d861-4f6c-8924-712bb44db658
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0398 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3184 : RatBall :=
  ⟨⟨123/640, -221/640⟩, 3/1280⟩
def center3184 : GaussianRat :=
  ⟨29748323/200000000, -119366383/500000000⟩
def contact3184 : RatBall := localContactBall tau3184 center3184
def work3184 : RoundedTauEval :=
  evalTau precision tau3184 contact3184 logTwoBall

theorem center_sq3184 : (center3184.re : ℝ)^2 +
    (center3184.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3184]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3184 : work3184.theta.ok = true ∧
    work3184.jac.invOK = true ∧ acceptsUnitSq work3184.out = true := by decide +kernel

def cell3184 : CellCertificate where
  tauBall := tau3184
  contactCenter := center3184
  contactBall := contact3184
  work := work3184
  center_sq := center_sq3184
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3184.1
  jac_ok := checks3184.2.1
  accepted := checks3184.2.2

def tau3185 : RatBall :=
  ⟨⟨25/128, -223/640⟩, 3/1280⟩
def center3185 : GaussianRat :=
  ⟨151411581/1000000000, -120348091/500000000⟩
def contact3185 : RatBall := localContactBall tau3185 center3185
def work3185 : RoundedTauEval :=
  evalTau precision tau3185 contact3185 logTwoBall

theorem center_sq3185 : (center3185.re : ℝ)^2 +
    (center3185.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3185]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3185 : work3185.theta.ok = true ∧
    work3185.jac.invOK = true ∧ acceptsUnitSq work3185.out = true := by decide +kernel

def cell3185 : CellCertificate where
  tauBall := tau3185
  contactCenter := center3185
  contactBall := contact3185
  work := work3185
  center_sq := center_sq3185
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3185.1
  jac_ok := checks3185.2.1
  accepted := checks3185.2.2

def tau3186 : RatBall :=
  ⟨⟨127/640, -223/640⟩, 3/1280⟩
def center3186 : GaussianRat :=
  ⟨153725769/1000000000, -120168019/500000000⟩
def contact3186 : RatBall := localContactBall tau3186 center3186
def work3186 : RoundedTauEval :=
  evalTau precision tau3186 contact3186 logTwoBall

theorem center_sq3186 : (center3186.re : ℝ)^2 +
    (center3186.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3186]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3186 : work3186.theta.ok = true ∧
    work3186.jac.invOK = true ∧ acceptsUnitSq work3186.out = true := by decide +kernel

def cell3186 : CellCertificate where
  tauBall := tau3186
  contactCenter := center3186
  contactBall := contact3186
  work := work3186
  center_sq := center_sq3186
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3186.1
  jac_ok := checks3186.2.1
  accepted := checks3186.2.2

def tau3187 : RatBall :=
  ⟨⟨25/128, -221/640⟩, 3/1280⟩
def center3187 : GaussianRat :=
  ⟨151056059/1000000000, -238381849/1000000000⟩
def contact3187 : RatBall := localContactBall tau3187 center3187
def work3187 : RoundedTauEval :=
  evalTau precision tau3187 contact3187 logTwoBall

theorem center_sq3187 : (center3187.re : ℝ)^2 +
    (center3187.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3187]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3187 : work3187.theta.ok = true ∧
    work3187.jac.invOK = true ∧ acceptsUnitSq work3187.out = true := by decide +kernel

def cell3187 : CellCertificate where
  tauBall := tau3187
  contactCenter := center3187
  contactBall := contact3187
  work := work3187
  center_sq := center_sq3187
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3187.1
  jac_ok := checks3187.2.1
  accepted := checks3187.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398


