-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0307_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0307_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:11:10.274719+00:00
-- url     : https://prove2.me/theorems/903a44c3-4c11-4225-9a73-a3fa570895a4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0307 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2456 : RatBall :=
  ⟨⟨89/320, 81/320⟩, 3/640⟩
def center2456 : GaussianRat :=
  ⟨199473497/1000000000, 41191221/250000000⟩
def contact2456 : RatBall := localContactBall tau2456 center2456
def work2456 : RoundedTauEval :=
  evalTau precision tau2456 contact2456 logTwoBall

theorem center_sq2456 : (center2456.re : ℝ)^2 +
    (center2456.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2456]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2456 : work2456.theta.ok = true ∧
    work2456.jac.invOK = true ∧ acceptsUnitSq work2456.out = true := by decide +kernel

def cell2456 : CellCertificate where
  tauBall := tau2456
  contactCenter := center2456
  contactBall := contact2456
  work := work2456
  center_sq := center_sq2456
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2456.1
  jac_ok := checks2456.2.1
  accepted := checks2456.2.2

def tau2457 : RatBall :=
  ⟨⟨91/320, 81/320⟩, 3/640⟩
def center2457 : GaussianRat :=
  ⟨101825843/500000000, 82077687/500000000⟩
def contact2457 : RatBall := localContactBall tau2457 center2457
def work2457 : RoundedTauEval :=
  evalTau precision tau2457 contact2457 logTwoBall

theorem center_sq2457 : (center2457.re : ℝ)^2 +
    (center2457.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2457]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2457 : work2457.theta.ok = true ∧
    work2457.jac.invOK = true ∧ acceptsUnitSq work2457.out = true := by decide +kernel

def cell2457 : CellCertificate where
  tauBall := tau2457
  contactCenter := center2457
  contactBall := contact2457
  work := work2457
  center_sq := center_sq2457
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2457.1
  jac_ok := checks2457.2.1
  accepted := checks2457.2.2

def tau2458 : RatBall :=
  ⟨⟨89/320, 83/320⟩, 3/640⟩
def center2458 : GaussianRat :=
  ⟨100043853/500000000, 84478333/500000000⟩
def contact2458 : RatBall := localContactBall tau2458 center2458
def work2458 : RoundedTauEval :=
  evalTau precision tau2458 contact2458 logTwoBall

theorem center_sq2458 : (center2458.re : ℝ)^2 +
    (center2458.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2458]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2458 : work2458.theta.ok = true ∧
    work2458.jac.invOK = true ∧ acceptsUnitSq work2458.out = true := by decide +kernel

def cell2458 : CellCertificate where
  tauBall := tau2458
  contactCenter := center2458
  contactBall := contact2458
  work := work2458
  center_sq := center_sq2458
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2458.1
  jac_ok := checks2458.2.1
  accepted := checks2458.2.2

def tau2459 : RatBall :=
  ⟨⟨91/320, 83/320⟩, 3/640⟩
def center2459 : GaussianRat :=
  ⟨204274783/1000000000, 168328783/1000000000⟩
def contact2459 : RatBall := localContactBall tau2459 center2459
def work2459 : RoundedTauEval :=
  evalTau precision tau2459 contact2459 logTwoBall

theorem center_sq2459 : (center2459.re : ℝ)^2 +
    (center2459.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2459]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2459 : work2459.theta.ok = true ∧
    work2459.jac.invOK = true ∧ acceptsUnitSq work2459.out = true := by decide +kernel

def cell2459 : CellCertificate where
  tauBall := tau2459
  contactCenter := center2459
  contactBall := contact2459
  work := work2459
  center_sq := center_sq2459
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2459.1
  jac_ok := checks2459.2.1
  accepted := checks2459.2.2

def tau2460 : RatBall :=
  ⟨⟨93/320, 81/320⟩, 3/640⟩
def center2460 : GaussianRat :=
  ⟨103905761/500000000, 163537217/1000000000⟩
def contact2460 : RatBall := localContactBall tau2460 center2460
def work2460 : RoundedTauEval :=
  evalTau precision tau2460 contact2460 logTwoBall

theorem center_sq2460 : (center2460.re : ℝ)^2 +
    (center2460.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2460]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2460 : work2460.theta.ok = true ∧
    work2460.jac.invOK = true ∧ acceptsUnitSq work2460.out = true := by decide +kernel

def cell2460 : CellCertificate where
  tauBall := tau2460
  contactCenter := center2460
  contactBall := contact2460
  work := work2460
  center_sq := center_sq2460
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2460.1
  jac_ok := checks2460.2.1
  accepted := checks2460.2.2

def tau2461 : RatBall :=
  ⟨⟨19/64, 81/320⟩, 3/640⟩
def center2461 : GaussianRat :=
  ⟨211952789/1000000000, 162910673/1000000000⟩
def contact2461 : RatBall := localContactBall tau2461 center2461
def work2461 : RoundedTauEval :=
  evalTau precision tau2461 contact2461 logTwoBall

theorem center_sq2461 : (center2461.re : ℝ)^2 +
    (center2461.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2461]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2461 : work2461.theta.ok = true ∧
    work2461.jac.invOK = true ∧ acceptsUnitSq work2461.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307


