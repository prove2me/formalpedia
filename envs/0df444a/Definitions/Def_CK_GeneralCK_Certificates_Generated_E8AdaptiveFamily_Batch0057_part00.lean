-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0057_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0057_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:44:54.985722+00:00
-- url     : https://prove2.me/theorems/98fc47e6-f13e-47e4-9d92-e8285cfc58c8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0057 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0456 : RatBall :=
  ⟨⟨-17/160, -9/32⟩, 3/320⟩
def center0456 : GaussianRat :=
  ⟨-19945259/250000000, -39579621/200000000⟩
def contact0456 : RatBall := localContactBall tau0456 center0456
def work0456 : RoundedTauEval :=
  evalTau precision tau0456 contact0456 logTwoBall

theorem center_sq0456 : (center0456.re : ℝ)^2 +
    (center0456.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0456]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0456 : work0456.theta.ok = true ∧
    work0456.jac.invOK = true ∧ acceptsUnitSq work0456.out = true := by decide +kernel

def cell0456 : CellCertificate where
  tauBall := tau0456
  contactCenter := center0456
  contactBall := contact0456
  work := work0456
  center_sq := center_sq0456
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0456.1
  jac_ok := checks0456.2.1
  accepted := checks0456.2.2

def tau0457 : RatBall :=
  ⟨⟨-23/160, -43/160⟩, 3/320⟩
def center0457 : GaussianRat :=
  ⟨-106644393/1000000000, -93309307/500000000⟩
def contact0457 : RatBall := localContactBall tau0457 center0457
def work0457 : RoundedTauEval :=
  evalTau precision tau0457 contact0457 logTwoBall

theorem center_sq0457 : (center0457.re : ℝ)^2 +
    (center0457.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0457]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0457 : work0457.theta.ok = true ∧
    work0457.jac.invOK = true ∧ acceptsUnitSq work0457.out = true := by decide +kernel

def cell0457 : CellCertificate where
  tauBall := tau0457
  contactCenter := center0457
  contactBall := contact0457
  work := work0457
  center_sq := center_sq0457
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0457.1
  jac_ok := checks0457.2.1
  accepted := checks0457.2.2

def tau0458 : RatBall :=
  ⟨⟨-21/160, -43/160⟩, 3/320⟩
def center0458 : GaussianRat :=
  ⟨-1523927/15625000, -46839637/250000000⟩
def contact0458 : RatBall := localContactBall tau0458 center0458
def work0458 : RoundedTauEval :=
  evalTau precision tau0458 contact0458 logTwoBall

theorem center_sq0458 : (center0458.re : ℝ)^2 +
    (center0458.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0458]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0458 : work0458.theta.ok = true ∧
    work0458.jac.invOK = true ∧ acceptsUnitSq work0458.out = true := by decide +kernel

def cell0458 : CellCertificate where
  tauBall := tau0458
  contactCenter := center0458
  contactBall := contact0458
  work := work0458
  center_sq := center_sq0458
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0458.1
  jac_ok := checks0458.2.1
  accepted := checks0458.2.2

def tau0459 : RatBall :=
  ⟨⟨-23/160, -41/160⟩, 3/320⟩
def center0459 : GaussianRat :=
  ⟨-105897059/1000000000, -22194707/125000000⟩
def contact0459 : RatBall := localContactBall tau0459 center0459
def work0459 : RoundedTauEval :=
  evalTau precision tau0459 contact0459 logTwoBall

theorem center_sq0459 : (center0459.re : ℝ)^2 +
    (center0459.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0459]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0459 : work0459.theta.ok = true ∧
    work0459.jac.invOK = true ∧ acceptsUnitSq work0459.out = true := by decide +kernel

def cell0459 : CellCertificate where
  tauBall := tau0459
  contactCenter := center0459
  contactBall := contact0459
  work := work0459
  center_sq := center_sq0459
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0459.1
  jac_ok := checks0459.2.1
  accepted := checks0459.2.2

def tau0460 : RatBall :=
  ⟨⟨-21/160, -41/160⟩, 3/320⟩
def center0460 : GaussianRat :=
  ⟨-96843181/1000000000, -5570429/31250000⟩
def contact0460 : RatBall := localContactBall tau0460 center0460
def work0460 : RoundedTauEval :=
  evalTau precision tau0460 contact0460 logTwoBall

theorem center_sq0460 : (center0460.re : ℝ)^2 +
    (center0460.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0460]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0460 : work0460.theta.ok = true ∧
    work0460.jac.invOK = true ∧ acceptsUnitSq work0460.out = true := by decide +kernel

def cell0460 : CellCertificate where
  tauBall := tau0460
  contactCenter := center0460
  contactBall := contact0460
  work := work0460
  center_sq := center_sq0460
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0460.1
  jac_ok := checks0460.2.1
  accepted := checks0460.2.2

def tau0461 : RatBall :=
  ⟨⟨-19/160, -43/160⟩, 3/320⟩
def center0461 : GaussianRat :=
  ⟨-88375401/1000000000, -188036739/1000000000⟩
def contact0461 : RatBall := localContactBall tau0461 center0461
def work0461 : RoundedTauEval :=
  evalTau precision tau0461 contact0461 logTwoBall

theorem center_sq0461 : (center0461.re : ℝ)^2 +
    (center0461.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0461]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0461 : work0461.theta.ok = true ∧
    work0461.jac.invOK = true ∧ acceptsUnitSq work0461.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057


