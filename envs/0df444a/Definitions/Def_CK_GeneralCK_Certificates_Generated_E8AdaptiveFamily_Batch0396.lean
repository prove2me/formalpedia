-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0396
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0396
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:08:34.151819+00:00
-- url     : https://prove2.me/theorems/0b6b516e-c4f0-4a46-874e-a4063119c8dd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0396.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0396_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3172 : work3172.theta.ok = true ∧
    work3172.jac.invOK = true ∧ acceptsUnitSq work3172.out = true := by decide +kernel

def cell3172 : CellCertificate where
  tauBall := tau3172
  contactCenter := center3172
  contactBall := contact3172
  work := work3172
  center_sq := center_sq3172
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3172.1
  jac_ok := checks3172.2.1
  accepted := checks3172.2.2

def tau3173 : RatBall :=
  ⟨⟨23/128, -45/128⟩, 3/1280⟩
def center3173 : GaussianRat :=
  ⟨5604287/40000000, -122385171/500000000⟩
def contact3173 : RatBall := localContactBall tau3173 center3173
def work3173 : RoundedTauEval :=
  evalTau precision tau3173 contact3173 logTwoBall

theorem center_sq3173 : (center3173.re : ℝ)^2 +
    (center3173.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3173]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3173 : work3173.theta.ok = true ∧
    work3173.jac.invOK = true ∧ acceptsUnitSq work3173.out = true := by decide +kernel

def cell3173 : CellCertificate where
  tauBall := tau3173
  contactCenter := center3173
  contactBall := contact3173
  work := work3173
  center_sq := center_sq3173
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3173.1
  jac_ok := checks3173.2.1
  accepted := checks3173.2.2

def tau3174 : RatBall :=
  ⟨⟨117/640, -227/640⟩, 3/1280⟩
def center3174 : GaussianRat :=
  ⟨142795751/1000000000, -246771071/1000000000⟩
def contact3174 : RatBall := localContactBall tau3174 center3174
def work3174 : RoundedTauEval :=
  evalTau precision tau3174 contact3174 logTwoBall

theorem center_sq3174 : (center3174.re : ℝ)^2 +
    (center3174.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3174]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3174 : work3174.theta.ok = true ∧
    work3174.jac.invOK = true ∧ acceptsUnitSq work3174.out = true := by decide +kernel

def cell3174 : CellCertificate where
  tauBall := tau3174
  contactCenter := center3174
  contactBall := contact3174
  work := work3174
  center_sq := center_sq3174
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3174.1
  jac_ok := checks3174.2.1
  accepted := checks3174.2.2

def tau3175 : RatBall :=
  ⟨⟨119/640, -227/640⟩, 3/1280⟩
def center3175 : GaussianRat :=
  ⟨145138173/1000000000, -123210011/500000000⟩
def contact3175 : RatBall := localContactBall tau3175 center3175
def work3175 : RoundedTauEval :=
  evalTau precision tau3175 contact3175 logTwoBall

theorem center_sq3175 : (center3175.re : ℝ)^2 +
    (center3175.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3175]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3175 : work3175.theta.ok = true ∧
    work3175.jac.invOK = true ∧ acceptsUnitSq work3175.out = true := by decide +kernel

def cell3175 : CellCertificate where
  tauBall := tau3175
  contactCenter := center3175
  contactBall := contact3175
  work := work3175
  center_sq := center_sq3175
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3175.1
  jac_ok := checks3175.2.1
  accepted := checks3175.2.2

def cells : List CellCertificate := [cell3168, cell3169, cell3170, cell3171, cell3172, cell3173, cell3174, cell3175]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396


