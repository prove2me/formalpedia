-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0059_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0059_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:13:56.396267+00:00
-- url     : https://prove2.me/theorems/be50c3cf-3d83-4b25-b404-14a37a6a8f1d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0059 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0472 : RatBall :=
  ⟨⟨-5/32, -37/160⟩, 3/320⟩
def center0472 : GaussianRat :=
  ⟨-113439149/1000000000, -158939613/1000000000⟩
def contact0472 : RatBall := localContactBall tau0472 center0472
def work0472 : RoundedTauEval :=
  evalTau precision tau0472 contact0472 logTwoBall

theorem center_sq0472 : (center0472.re : ℝ)^2 +
    (center0472.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0472]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0472 : work0472.theta.ok = true ∧
    work0472.jac.invOK = true ∧ acceptsUnitSq work0472.out = true := by decide +kernel

def cell0472 : CellCertificate where
  tauBall := tau0472
  contactCenter := center0472
  contactBall := contact0472
  work := work0472
  center_sq := center_sq0472
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0472.1
  jac_ok := checks0472.2.1
  accepted := checks0472.2.2

def tau0473 : RatBall :=
  ⟨⟨-3/32, -47/160⟩, 3/320⟩
def center0473 : GaussianRat :=
  ⟨-71049459/1000000000, -207833009/1000000000⟩
def contact0473 : RatBall := localContactBall tau0473 center0473
def work0473 : RoundedTauEval :=
  evalTau precision tau0473 contact0473 logTwoBall

theorem center_sq0473 : (center0473.re : ℝ)^2 +
    (center0473.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0473]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0473 : work0473.theta.ok = true ∧
    work0473.jac.invOK = true ∧ acceptsUnitSq work0473.out = true := by decide +kernel

def cell0473 : CellCertificate where
  tauBall := tau0473
  contactCenter := center0473
  contactBall := contact0473
  work := work0473
  center_sq := center_sq0473
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0473.1
  jac_ok := checks0473.2.1
  accepted := checks0473.2.2

def tau0474 : RatBall :=
  ⟨⟨-13/160, -47/160⟩, 3/320⟩
def center0474 : GaussianRat :=
  ⟨-61646237/1000000000, -5209469/25000000⟩
def contact0474 : RatBall := localContactBall tau0474 center0474
def work0474 : RoundedTauEval :=
  evalTau precision tau0474 contact0474 logTwoBall

theorem center_sq0474 : (center0474.re : ℝ)^2 +
    (center0474.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0474]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0474 : work0474.theta.ok = true ∧
    work0474.jac.invOK = true ∧ acceptsUnitSq work0474.out = true := by decide +kernel

def cell0474 : CellCertificate where
  tauBall := tau0474
  contactCenter := center0474
  contactBall := contact0474
  work := work0474
  center_sq := center_sq0474
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0474.1
  jac_ok := checks0474.2.1
  accepted := checks0474.2.2

def tau0475 : RatBall :=
  ⟨⟨-3/32, -9/32⟩, 3/320⟩
def center0475 : GaussianRat :=
  ⟨-17620809/250000000, -24810311/125000000⟩
def contact0475 : RatBall := localContactBall tau0475 center0475
def work0475 : RoundedTauEval :=
  evalTau precision tau0475 contact0475 logTwoBall

theorem center_sq0475 : (center0475.re : ℝ)^2 +
    (center0475.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0475]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0475 : work0475.theta.ok = true ∧
    work0475.jac.invOK = true ∧ acceptsUnitSq work0475.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059


