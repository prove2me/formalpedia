-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0431_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0431_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:18:21.027209+00:00
-- url     : https://prove2.me/theorems/9d441310-7df7-473b-93bc-2a759e22e833
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0431 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3448 : RatBall :=
  ⟨⟨-31/640, 49/128⟩, 3/1280⟩
def center3448 : GaussianRat :=
  ⟨-19763727/500000000, 279288009/1000000000⟩
def contact3448 : RatBall := localContactBall tau3448 center3448
def work3448 : RoundedTauEval :=
  evalTau precision tau3448 contact3448 logTwoBall

theorem center_sq3448 : (center3448.re : ℝ)^2 +
    (center3448.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3448]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3448 : work3448.theta.ok = true ∧
    work3448.jac.invOK = true ∧ acceptsUnitSq work3448.out = true := by decide +kernel

def cell3448 : CellCertificate where
  tauBall := tau3448
  contactCenter := center3448
  contactBall := contact3448
  work := work3448
  center_sq := center_sq3448
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3448.1
  jac_ok := checks3448.2.1
  accepted := checks3448.2.2

def tau3449 : RatBall :=
  ⟨⟨-29/640, 49/128⟩, 3/1280⟩
def center3449 : GaussianRat :=
  ⟨-4623097/125000000, 13969953/50000000⟩
def contact3449 : RatBall := localContactBall tau3449 center3449
def work3449 : RoundedTauEval :=
  evalTau precision tau3449 contact3449 logTwoBall

theorem center_sq3449 : (center3449.re : ℝ)^2 +
    (center3449.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3449]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3449 : work3449.theta.ok = true ∧
    work3449.jac.invOK = true ∧ acceptsUnitSq work3449.out = true := by decide +kernel

def cell3449 : CellCertificate where
  tauBall := tau3449
  contactCenter := center3449
  contactBall := contact3449
  work := work3449
  center_sq := center_sq3449
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3449.1
  jac_ok := checks3449.2.1
  accepted := checks3449.2.2

def tau3450 : RatBall :=
  ⟨⟨-31/640, 247/640⟩, 3/1280⟩
def center3450 : GaussianRat :=
  ⟨-4955369/125000000, 8807299/31250000⟩
def contact3450 : RatBall := localContactBall tau3450 center3450
def work3450 : RoundedTauEval :=
  evalTau precision tau3450 contact3450 logTwoBall

theorem center_sq3450 : (center3450.re : ℝ)^2 +
    (center3450.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3450]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3450 : work3450.theta.ok = true ∧
    work3450.jac.invOK = true ∧ acceptsUnitSq work3450.out = true := by decide +kernel

def cell3450 : CellCertificate where
  tauBall := tau3450
  contactCenter := center3450
  contactBall := contact3450
  work := work3450
  center_sq := center_sq3450
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3450.1
  jac_ok := checks3450.2.1
  accepted := checks3450.2.2

def tau3451 : RatBall :=
  ⟨⟨-29/640, 247/640⟩, 3/1280⟩
def center3451 : GaussianRat :=
  ⟨-18546463/500000000, 281946171/1000000000⟩
def contact3451 : RatBall := localContactBall tau3451 center3451
def work3451 : RoundedTauEval :=
  evalTau precision tau3451 contact3451 logTwoBall

theorem center_sq3451 : (center3451.re : ℝ)^2 +
    (center3451.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3451]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3451 : work3451.theta.ok = true ∧
    work3451.jac.invOK = true ∧ acceptsUnitSq work3451.out = true := by decide +kernel

def cell3451 : CellCertificate where
  tauBall := tau3451
  contactCenter := center3451
  contactBall := contact3451
  work := work3451
  center_sq := center_sq3451
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3451.1
  jac_ok := checks3451.2.1
  accepted := checks3451.2.2

def tau3452 : RatBall :=
  ⟨⟨-27/640, 49/128⟩, 3/1280⟩
def center3452 : GaussianRat :=
  ⟨-1076269/31250000, 69875701/250000000⟩
def contact3452 : RatBall := localContactBall tau3452 center3452
def work3452 : RoundedTauEval :=
  evalTau precision tau3452 contact3452 logTwoBall

theorem center_sq3452 : (center3452.re : ℝ)^2 +
    (center3452.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3452]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3452 : work3452.theta.ok = true ∧
    work3452.jac.invOK = true ∧ acceptsUnitSq work3452.out = true := by decide +kernel

def cell3452 : CellCertificate where
  tauBall := tau3452
  contactCenter := center3452
  contactBall := contact3452
  work := work3452
  center_sq := center_sq3452
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3452.1
  jac_ok := checks3452.2.1
  accepted := checks3452.2.2

def tau3453 : RatBall :=
  ⟨⟨-5/128, 49/128⟩, 3/1280⟩
def center3453 : GaussianRat :=
  ⟨-31895051/1000000000, 13979961/50000000⟩
def contact3453 : RatBall := localContactBall tau3453 center3453
def work3453 : RoundedTauEval :=
  evalTau precision tau3453 contact3453 logTwoBall

theorem center_sq3453 : (center3453.re : ℝ)^2 +
    (center3453.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3453]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3453 : work3453.theta.ok = true ∧
    work3453.jac.invOK = true ∧ acceptsUnitSq work3453.out = true := by decide +kernel

def cell3453 : CellCertificate where
  tauBall := tau3453
  contactCenter := center3453
  contactBall := contact3453
  work := work3453
  center_sq := center_sq3453
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3453.1
  jac_ok := checks3453.2.1
  accepted := checks3453.2.2

def tau3454 : RatBall :=
  ⟨⟨-27/640, 247/640⟩, 3/1280⟩
def center3454 : GaussianRat :=
  ⟨-34541389/1000000000, 56410273/200000000⟩
def contact3454 : RatBall := localContactBall tau3454 center3454
def work3454 : RoundedTauEval :=
  evalTau precision tau3454 contact3454 logTwoBall

theorem center_sq3454 : (center3454.re : ℝ)^2 +
    (center3454.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3454]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431


