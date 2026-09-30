-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0341_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0341_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:04:50.523602+00:00
-- url     : https://prove2.me/theorems/d2ea6488-958f-40ca-a9a9-bd80386810a4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0341 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2728 : RatBall :=
  ⟨⟨-53/640, -249/640⟩, 3/1280⟩
def center2728 : GaussianRat :=
  ⟨-33881037/500000000, -282642041/1000000000⟩
def contact2728 : RatBall := localContactBall tau2728 center2728
def work2728 : RoundedTauEval :=
  evalTau precision tau2728 contact2728 logTwoBall

theorem center_sq2728 : (center2728.re : ℝ)^2 +
    (center2728.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2728]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2728 : work2728.theta.ok = true ∧
    work2728.jac.invOK = true ∧ acceptsUnitSq work2728.out = true := by decide +kernel

def cell2728 : CellCertificate where
  tauBall := tau2728
  contactCenter := center2728
  contactBall := contact2728
  work := work2728
  center_sq := center_sq2728
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2728.1
  jac_ok := checks2728.2.1
  accepted := checks2728.2.2

def tau2729 : RatBall :=
  ⟨⟨-51/640, -251/640⟩, 3/1280⟩
def center2729 : GaussianRat :=
  ⟨-65420927/1000000000, -285375989/1000000000⟩
def contact2729 : RatBall := localContactBall tau2729 center2729
def work2729 : RoundedTauEval :=
  evalTau precision tau2729 contact2729 logTwoBall

theorem center_sq2729 : (center2729.re : ℝ)^2 +
    (center2729.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2729]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2729 : work2729.theta.ok = true ∧
    work2729.jac.invOK = true ∧ acceptsUnitSq work2729.out = true := by decide +kernel

def cell2729 : CellCertificate where
  tauBall := tau2729
  contactCenter := center2729
  contactBall := contact2729
  work := work2729
  center_sq := center_sq2729
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2729.1
  jac_ok := checks2729.2.1
  accepted := checks2729.2.2

def tau2730 : RatBall :=
  ⟨⟨-49/640, -251/640⟩, 3/1280⟩
def center2730 : GaussianRat :=
  ⟨-6287709/100000000, -142783229/500000000⟩
def contact2730 : RatBall := localContactBall tau2730 center2730
def work2730 : RoundedTauEval :=
  evalTau precision tau2730 contact2730 logTwoBall

theorem center_sq2730 : (center2730.re : ℝ)^2 +
    (center2730.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2730]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2730 : work2730.theta.ok = true ∧
    work2730.jac.invOK = true ∧ acceptsUnitSq work2730.out = true := by decide +kernel

def cell2730 : CellCertificate where
  tauBall := tau2730
  contactCenter := center2730
  contactBall := contact2730
  work := work2730
  center_sq := center_sq2730
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2730.1
  jac_ok := checks2730.2.1
  accepted := checks2730.2.2

def tau2731 : RatBall :=
  ⟨⟨-51/640, -249/640⟩, 3/1280⟩
def center2731 : GaussianRat :=
  ⟨-13045627/200000000, -141418551/500000000⟩
def contact2731 : RatBall := localContactBall tau2731 center2731
def work2731 : RoundedTauEval :=
  evalTau precision tau2731 contact2731 logTwoBall

theorem center_sq2731 : (center2731.re : ℝ)^2 +
    (center2731.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2731]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2731 : work2731.theta.ok = true ∧
    work2731.jac.invOK = true ∧ acceptsUnitSq work2731.out = true := by decide +kernel

def cell2731 : CellCertificate where
  tauBall := tau2731
  contactCenter := center2731
  contactBall := contact2731
  work := work2731
  center_sq := center_sq2731
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2731.1
  jac_ok := checks2731.2.1
  accepted := checks2731.2.2

def tau2732 : RatBall :=
  ⟨⟨-49/640, -249/640⟩, 3/1280⟩
def center2732 : GaussianRat :=
  ⟨-62691561/1000000000, -141512483/500000000⟩
def contact2732 : RatBall := localContactBall tau2732 center2732
def work2732 : RoundedTauEval :=
  evalTau precision tau2732 contact2732 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341


