-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0262_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0262_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:51:41.052455+00:00
-- url     : https://prove2.me/theorems/95511bdc-d6f1-45a1-8575-e1ca07fb2400
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0262 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2096 : RatBall :=
  ⟨⟨-9/64, 111/320⟩, 3/640⟩
def center2096 : GaussianRat :=
  ⟨-4402271/40000000, 122514671/500000000⟩
def contact2096 : RatBall := localContactBall tau2096 center2096
def work2096 : RoundedTauEval :=
  evalTau precision tau2096 contact2096 logTwoBall

theorem center_sq2096 : (center2096.re : ℝ)^2 +
    (center2096.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2096]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2096 : work2096.theta.ok = true ∧
    work2096.jac.invOK = true ∧ acceptsUnitSq work2096.out = true := by decide +kernel

def cell2096 : CellCertificate where
  tauBall := tau2096
  contactCenter := center2096
  contactBall := contact2096
  work := work2096
  center_sq := center_sq2096
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2096.1
  jac_ok := checks2096.2.1
  accepted := checks2096.2.2

def tau2097 : RatBall :=
  ⟨⟨-43/320, 109/320⟩, 3/640⟩
def center2097 : GaussianRat :=
  ⟨-26190451/250000000, 3762143/15625000⟩
def contact2097 : RatBall := localContactBall tau2097 center2097
def work2097 : RoundedTauEval :=
  evalTau precision tau2097 contact2097 logTwoBall

theorem center_sq2097 : (center2097.re : ℝ)^2 +
    (center2097.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2097]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2097 : work2097.theta.ok = true ∧
    work2097.jac.invOK = true ∧ acceptsUnitSq work2097.out = true := by decide +kernel

def cell2097 : CellCertificate where
  tauBall := tau2097
  contactCenter := center2097
  contactBall := contact2097
  work := work2097
  center_sq := center_sq2097
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2097.1
  jac_ok := checks2097.2.1
  accepted := checks2097.2.2

def tau2098 : RatBall :=
  ⟨⟨-41/320, 109/320⟩, 3/640⟩
def center2098 : GaussianRat :=
  ⟨-6249053/62500000, 241270351/1000000000⟩
def contact2098 : RatBall := localContactBall tau2098 center2098
def work2098 : RoundedTauEval :=
  evalTau precision tau2098 contact2098 logTwoBall

theorem center_sq2098 : (center2098.re : ℝ)^2 +
    (center2098.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2098]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2098 : work2098.theta.ok = true ∧
    work2098.jac.invOK = true ∧ acceptsUnitSq work2098.out = true := by decide +kernel

def cell2098 : CellCertificate where
  tauBall := tau2098
  contactCenter := center2098
  contactBall := contact2098
  work := work2098
  center_sq := center_sq2098
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2098.1
  jac_ok := checks2098.2.1
  accepted := checks2098.2.2

def tau2099 : RatBall :=
  ⟨⟨-43/320, 111/320⟩, 3/640⟩
def center2099 : GaussianRat :=
  ⟨-21054511/200000000, 122778933/500000000⟩
def contact2099 : RatBall := localContactBall tau2099 center2099
def work2099 : RoundedTauEval :=
  evalTau precision tau2099 contact2099 logTwoBall

theorem center_sq2099 : (center2099.re : ℝ)^2 +
    (center2099.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2099]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2099 : work2099.theta.ok = true ∧
    work2099.jac.invOK = true ∧ acceptsUnitSq work2099.out = true := by decide +kernel

def cell2099 : CellCertificate where
  tauBall := tau2099
  contactCenter := center2099
  contactBall := contact2099
  work := work2099
  center_sq := center_sq2099
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2099.1
  jac_ok := checks2099.2.1
  accepted := checks2099.2.2

def tau2100 : RatBall :=
  ⟨⟨-41/320, 111/320⟩, 3/640⟩
def center2100 : GaussianRat :=
  ⟨-100474143/1000000000, 123032409/500000000⟩
def contact2100 : RatBall := localContactBall tau2100 center2100
def work2100 : RoundedTauEval :=
  evalTau precision tau2100 contact2100 logTwoBall

theorem center_sq2100 : (center2100.re : ℝ)^2 +
    (center2100.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2100]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2100 : work2100.theta.ok = true ∧
    work2100.jac.invOK = true ∧ acceptsUnitSq work2100.out = true := by decide +kernel

def cell2100 : CellCertificate where
  tauBall := tau2100
  contactCenter := center2100
  contactBall := contact2100
  work := work2100
  center_sq := center_sq2100
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2100.1
  jac_ok := checks2100.2.1
  accepted := checks2100.2.2

def tau2101 : RatBall :=
  ⟨⟨-39/320, 21/64⟩, 3/640⟩
def center2101 : GaussianRat :=
  ⟨-94297493/1000000000, 185753/800000⟩
def contact2101 : RatBall := localContactBall tau2101 center2101
def work2101 : RoundedTauEval :=
  evalTau precision tau2101 contact2101 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262


