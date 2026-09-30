-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0276_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0276_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:21:22.142477+00:00
-- url     : https://prove2.me/theorems/25934717-9125-4b29-9272-9a4e2f714571
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0276 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2208 : RatBall :=
  ⟨⟨-3/320, 119/320⟩, 3/640⟩
def center2208 : GaussianRat :=
  ⟨-3793023/500000000, 135626627/500000000⟩
def contact2208 : RatBall := localContactBall tau2208 center2208
def work2208 : RoundedTauEval :=
  evalTau precision tau2208 contact2208 logTwoBall

theorem center_sq2208 : (center2208.re : ℝ)^2 +
    (center2208.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2208]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2208 : work2208.theta.ok = true ∧
    work2208.jac.invOK = true ∧ acceptsUnitSq work2208.out = true := by decide +kernel

def cell2208 : CellCertificate where
  tauBall := tau2208
  contactCenter := center2208
  contactBall := contact2208
  work := work2208
  center_sq := center_sq2208
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2208.1
  jac_ok := checks2208.2.1
  accepted := checks2208.2.2

def tau2209 : RatBall :=
  ⟨⟨-1/320, 119/320⟩, 3/640⟩
def center2209 : GaussianRat :=
  ⟨-1264407/500000000, 33910207/125000000⟩
def contact2209 : RatBall := localContactBall tau2209 center2209
def work2209 : RoundedTauEval :=
  evalTau precision tau2209 contact2209 logTwoBall

theorem center_sq2209 : (center2209.re : ℝ)^2 +
    (center2209.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2209]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2209 : work2209.theta.ok = true ∧
    work2209.jac.invOK = true ∧ acceptsUnitSq work2209.out = true := by decide +kernel

def cell2209 : CellCertificate where
  tauBall := tau2209
  contactCenter := center2209
  contactBall := contact2209
  work := work2209
  center_sq := center_sq2209
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2209.1
  jac_ok := checks2209.2.1
  accepted := checks2209.2.2

def tau2210 : RatBall :=
  ⟨⟨-3/64, 121/320⟩, 3/640⟩
def center2210 : GaussianRat :=
  ⟨-38091451/1000000000, 137769289/500000000⟩
def contact2210 : RatBall := localContactBall tau2210 center2210
def work2210 : RoundedTauEval :=
  evalTau precision tau2210 contact2210 logTwoBall

theorem center_sq2210 : (center2210.re : ℝ)^2 +
    (center2210.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2210]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2210 : work2210.theta.ok = true ∧
    work2210.jac.invOK = true ∧ acceptsUnitSq work2210.out = true := by decide +kernel

def cell2210 : CellCertificate where
  tauBall := tau2210
  contactCenter := center2210
  contactBall := contact2210
  work := work2210
  center_sq := center_sq2210
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2210.1
  jac_ok := checks2210.2.1
  accepted := checks2210.2.2

def tau2211 : RatBall :=
  ⟨⟨-13/320, 121/320⟩, 3/640⟩
def center2211 : GaussianRat :=
  ⟨-8256217/250000000, 34467723/125000000⟩
def contact2211 : RatBall := localContactBall tau2211 center2211
def work2211 : RoundedTauEval :=
  evalTau precision tau2211 contact2211 logTwoBall

theorem center_sq2211 : (center2211.re : ℝ)^2 +
    (center2211.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2211]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2211 : work2211.theta.ok = true ∧
    work2211.jac.invOK = true ∧ acceptsUnitSq work2211.out = true := by decide +kernel

def cell2211 : CellCertificate where
  tauBall := tau2211
  contactCenter := center2211
  contactBall := contact2211
  work := work2211
  center_sq := center_sq2211
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2211.1
  jac_ok := checks2211.2.1
  accepted := checks2211.2.2

def tau2212 : RatBall :=
  ⟨⟨-11/320, 121/320⟩, 3/640⟩
def center2212 : GaussianRat :=
  ⟨-27953037/1000000000, 55183249/200000000⟩
def contact2212 : RatBall := localContactBall tau2212 center2212
def work2212 : RoundedTauEval :=
  evalTau precision tau2212 contact2212 logTwoBall

theorem center_sq2212 : (center2212.re : ℝ)^2 +
    (center2212.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2212]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2212 : work2212.theta.ok = true ∧
    work2212.jac.invOK = true ∧ acceptsUnitSq work2212.out = true := by decide +kernel

def cell2212 : CellCertificate where
  tauBall := tau2212
  contactCenter := center2212
  contactBall := contact2212
  work := work2212
  center_sq := center_sq2212
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2212.1
  jac_ok := checks2212.2.1
  accepted := checks2212.2.2

def tau2213 : RatBall :=
  ⟨⟨-9/320, 121/320⟩, 3/640⟩
def center2213 : GaussianRat :=
  ⟨-4575351/200000000, 276061831/1000000000⟩
def contact2213 : RatBall := localContactBall tau2213 center2213
def work2213 : RoundedTauEval :=
  evalTau precision tau2213 contact2213 logTwoBall

theorem center_sq2213 : (center2213.re : ℝ)^2 +
    (center2213.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2213]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2213 : work2213.theta.ok = true ∧
    work2213.jac.invOK = true ∧ acceptsUnitSq work2213.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276


