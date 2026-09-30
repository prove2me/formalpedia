-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0384_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0384_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:51:12.006785+00:00
-- url     : https://prove2.me/theorems/b1c0e8e7-cbdc-46bb-a873-f618a0c5fd02
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0384 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3072 : RatBall :=
  ⟨⟨77/640, -241/640⟩, 3/1280⟩
def center3072 : GaussianRat :=
  ⟨96833401/1000000000, -8432309/31250000⟩
def contact3072 : RatBall := localContactBall tau3072 center3072
def work3072 : RoundedTauEval :=
  evalTau precision tau3072 contact3072 logTwoBall

theorem center_sq3072 : (center3072.re : ℝ)^2 +
    (center3072.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3072]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3072 : work3072.theta.ok = true ∧
    work3072.jac.invOK = true ∧ acceptsUnitSq work3072.out = true := by decide +kernel

def cell3072 : CellCertificate where
  tauBall := tau3072
  contactCenter := center3072
  contactBall := contact3072
  work := work3072
  center_sq := center_sq3072
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3072.1
  jac_ok := checks3072.2.1
  accepted := checks3072.2.2

def tau3073 : RatBall :=
  ⟨⟨79/640, -241/640⟩, 3/1280⟩
def center3073 : GaussianRat :=
  ⟨99298877/1000000000, -134782023/500000000⟩
def contact3073 : RatBall := localContactBall tau3073 center3073
def work3073 : RoundedTauEval :=
  evalTau precision tau3073 contact3073 logTwoBall

theorem center_sq3073 : (center3073.re : ℝ)^2 +
    (center3073.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3073]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3073 : work3073.theta.ok = true ∧
    work3073.jac.invOK = true ∧ acceptsUnitSq work3073.out = true := by decide +kernel

def cell3073 : CellCertificate where
  tauBall := tau3073
  contactCenter := center3073
  contactBall := contact3073
  work := work3073
  center_sq := center_sq3073
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3073.1
  jac_ok := checks3073.2.1
  accepted := checks3073.2.2

def tau3074 : RatBall :=
  ⟨⟨81/640, -243/640⟩, 3/1280⟩
def center3074 : GaussianRat :=
  ⟨51020881/500000000, -135875479/500000000⟩
def contact3074 : RatBall := localContactBall tau3074 center3074
def work3074 : RoundedTauEval :=
  evalTau precision tau3074 contact3074 logTwoBall

theorem center_sq3074 : (center3074.re : ℝ)^2 +
    (center3074.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3074]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3074 : work3074.theta.ok = true ∧
    work3074.jac.invOK = true ∧ acceptsUnitSq work3074.out = true := by decide +kernel

def cell3074 : CellCertificate where
  tauBall := tau3074
  contactCenter := center3074
  contactBall := contact3074
  work := work3074
  center_sq := center_sq3074
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3074.1
  jac_ok := checks3074.2.1
  accepted := checks3074.2.2

def tau3075 : RatBall :=
  ⟨⟨83/640, -243/640⟩, 3/1280⟩
def center3075 : GaussianRat :=
  ⟨4180239/40000000, -271464801/1000000000⟩
def contact3075 : RatBall := localContactBall tau3075 center3075
def work3075 : RoundedTauEval :=
  evalTau precision tau3075 contact3075 logTwoBall

theorem center_sq3075 : (center3075.re : ℝ)^2 +
    (center3075.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3075]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3075 : work3075.theta.ok = true ∧
    work3075.jac.invOK = true ∧ acceptsUnitSq work3075.out = true := by decide +kernel

def cell3075 : CellCertificate where
  tauBall := tau3075
  contactCenter := center3075
  contactBall := contact3075
  work := work3075
  center_sq := center_sq3075
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3075.1
  jac_ok := checks3075.2.1
  accepted := checks3075.2.2

def tau3076 : RatBall :=
  ⟨⟨81/640, -241/640⟩, 3/1280⟩
def center3076 : GaussianRat :=
  ⟨101760649/1000000000, -269287947/1000000000⟩
def contact3076 : RatBall := localContactBall tau3076 center3076

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384


