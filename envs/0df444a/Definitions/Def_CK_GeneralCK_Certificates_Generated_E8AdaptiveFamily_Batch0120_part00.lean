-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0120_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0120_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:22:00.179237+00:00
-- url     : https://prove2.me/theorems/02e7f1aa-8b07-4f52-b50c-5986b7a4bcb8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0120 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0960 : RatBall :=
  ⟨⟨-11/160, 49/160⟩, 3/320⟩
def center0960 : GaussianRat :=
  ⟨-52658297/1000000000, 109167283/500000000⟩
def contact0960 : RatBall := localContactBall tau0960 center0960
def work0960 : RoundedTauEval :=
  evalTau precision tau0960 contact0960 logTwoBall

theorem center_sq0960 : (center0960.re : ℝ)^2 +
    (center0960.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0960]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0960 : work0960.theta.ok = true ∧
    work0960.jac.invOK = true ∧ acceptsUnitSq work0960.out = true := by decide +kernel

def cell0960 : CellCertificate where
  tauBall := tau0960
  contactCenter := center0960
  contactBall := contact0960
  work := work0960
  center_sq := center_sq0960
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0960.1
  jac_ok := checks0960.2.1
  accepted := checks0960.2.2

def tau0961 : RatBall :=
  ⟨⟨-9/160, 49/160⟩, 3/320⟩
def center0961 : GaussianRat :=
  ⟨-43120523/1000000000, 109375967/500000000⟩
def contact0961 : RatBall := localContactBall tau0961 center0961
def work0961 : RoundedTauEval :=
  evalTau precision tau0961 contact0961 logTwoBall

theorem center_sq0961 : (center0961.re : ℝ)^2 +
    (center0961.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0961]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0961 : work0961.theta.ok = true ∧
    work0961.jac.invOK = true ∧ acceptsUnitSq work0961.out = true := by decide +kernel

def cell0961 : CellCertificate where
  tauBall := tau0961
  contactCenter := center0961
  contactBall := contact0961
  work := work0961
  center_sq := center_sq0961
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0961.1
  jac_ok := checks0961.2.1
  accepted := checks0961.2.2

def tau0962 : RatBall :=
  ⟨⟨-11/160, 51/160⟩, 3/320⟩
def center0962 : GaussianRat :=
  ⟨-53129867/1000000000, 56975307/250000000⟩
def contact0962 : RatBall := localContactBall tau0962 center0962
def work0962 : RoundedTauEval :=
  evalTau precision tau0962 contact0962 logTwoBall

theorem center_sq0962 : (center0962.re : ℝ)^2 +
    (center0962.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0962]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0962 : work0962.theta.ok = true ∧
    work0962.jac.invOK = true ∧ acceptsUnitSq work0962.out = true := by decide +kernel

def cell0962 : CellCertificate where
  tauBall := tau0962
  contactCenter := center0962
  contactBall := contact0962
  work := work0962
  center_sq := center_sq0962
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0962.1
  jac_ok := checks0962.2.1
  accepted := checks0962.2.2

def tau0963 : RatBall :=
  ⟨⟨-9/160, 51/160⟩, 3/320⟩
def center0963 : GaussianRat :=
  ⟨-21754011/500000000, 445983/1953125⟩
def contact0963 : RatBall := localContactBall tau0963 center0963
def work0963 : RoundedTauEval :=
  evalTau precision tau0963 contact0963 logTwoBall

theorem center_sq0963 : (center0963.re : ℝ)^2 +
    (center0963.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0963]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0963 : work0963.theta.ok = true ∧
    work0963.jac.invOK = true ∧ acceptsUnitSq work0963.out = true := by decide +kernel

def cell0963 : CellCertificate where
  tauBall := tau0963
  contactCenter := center0963
  contactBall := contact0963
  work := work0963
  center_sq := center_sq0963
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0963.1
  jac_ok := checks0963.2.1
  accepted := checks0963.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120


