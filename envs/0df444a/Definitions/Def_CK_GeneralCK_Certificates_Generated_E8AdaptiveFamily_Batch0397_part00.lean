-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0397_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0397_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:30:56.962748+00:00
-- url     : https://prove2.me/theorems/06b46120-518b-4cb9-8423-62c62d084c91
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0397 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3176 : RatBall :=
  ⟨⟨117/640, -45/128⟩, 3/1280⟩
def center3176 : GaussianRat :=
  ⟨8903089/62500000, -244428717/1000000000⟩
def contact3176 : RatBall := localContactBall tau3176 center3176
def work3176 : RoundedTauEval :=
  evalTau precision tau3176 contact3176 logTwoBall

theorem center_sq3176 : (center3176.re : ℝ)^2 +
    (center3176.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3176]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3176 : work3176.theta.ok = true ∧
    work3176.jac.invOK = true ∧ acceptsUnitSq work3176.out = true := by decide +kernel

def cell3176 : CellCertificate where
  tauBall := tau3176
  contactCenter := center3176
  contactBall := contact3176
  work := work3176
  center_sq := center_sq3176
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3176.1
  jac_ok := checks3176.2.1
  accepted := checks3176.2.2

def tau3177 : RatBall :=
  ⟨⟨119/640, -45/128⟩, 3/1280⟩
def center3177 : GaussianRat :=
  ⟨72393537/500000000, -122041161/500000000⟩
def contact3177 : RatBall := localContactBall tau3177 center3177
def work3177 : RoundedTauEval :=
  evalTau precision tau3177 contact3177 logTwoBall

theorem center_sq3177 : (center3177.re : ℝ)^2 +
    (center3177.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3177]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3177 : work3177.theta.ok = true ∧
    work3177.jac.invOK = true ∧ acceptsUnitSq work3177.out = true := by decide +kernel

def cell3177 : CellCertificate where
  tauBall := tau3177
  contactCenter := center3177
  contactBall := contact3177
  work := work3177
  center_sq := center_sq3177
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3177.1
  jac_ok := checks3177.2.1
  accepted := checks3177.2.2

def tau3178 : RatBall :=
  ⟨⟨121/640, -227/640⟩, 3/1280⟩
def center3178 : GaussianRat :=
  ⟨147475889/1000000000, -123032099/500000000⟩
def contact3178 : RatBall := localContactBall tau3178 center3178
def work3178 : RoundedTauEval :=
  evalTau precision tau3178 contact3178 logTwoBall

theorem center_sq3178 : (center3178.re : ℝ)^2 +
    (center3178.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3178]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3178 : work3178.theta.ok = true ∧
    work3178.jac.invOK = true ∧ acceptsUnitSq work3178.out = true := by decide +kernel

def cell3178 : CellCertificate where
  tauBall := tau3178
  contactCenter := center3178
  contactBall := contact3178
  work := work3178
  center_sq := center_sq3178
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3178.1
  jac_ok := checks3178.2.1
  accepted := checks3178.2.2

def tau3179 : RatBall :=
  ⟨⟨121/640, -45/128⟩, 3/1280⟩
def center3179 : GaussianRat :=
  ⟨36780017/250000000, -243731207/1000000000⟩
def contact3179 : RatBall := localContactBall tau3179 center3179
def work3179 : RoundedTauEval :=
  evalTau precision tau3179 contact3179 logTwoBall

theorem center_sq3179 : (center3179.re : ℝ)^2 +
    (center3179.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3179]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3179 : work3179.theta.ok = true ∧
    work3179.jac.invOK = true ∧ acceptsUnitSq work3179.out = true := by decide +kernel

def cell3179 : CellCertificate where
  tauBall := tau3179
  contactCenter := center3179
  contactBall := contact3179
  work := work3179
  center_sq := center_sq3179
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3179.1
  jac_ok := checks3179.2.1
  accepted := checks3179.2.2

def tau3180 : RatBall :=
  ⟨⟨123/640, -45/128⟩, 3/1280⟩
def center3180 : GaussianRat :=
  ⟨149448351/1000000000, -9735017/40000000⟩
def contact3180 : RatBall := localContactBall tau3180 center3180
def work3180 : RoundedTauEval :=
  evalTau precision tau3180 contact3180 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397


