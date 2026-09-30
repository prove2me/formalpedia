-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0034_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0034_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:10:32.754025+00:00
-- url     : https://prove2.me/theorems/97f3957a-f8c4-4466-b442-24c29870d562
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0034 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0034_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0276 : RatBall :=
  ⟨⟨3/16, 9/80⟩, 3/160⟩
def center0276 : GaussianRat :=
  ⟨26005447/200000000, 37751763/500000000⟩
def contact0276 : RatBall := localContactBall tau0276 center0276
def work0276 : RoundedTauEval :=
  evalTau precision tau0276 contact0276 logTwoBall

theorem center_sq0276 : (center0276.re : ℝ)^2 +
    (center0276.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0276]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0276 : work0276.theta.ok = true ∧
    work0276.jac.invOK = true ∧ acceptsUnitSq work0276.out = true := by decide +kernel

def cell0276 : CellCertificate where
  tauBall := tau0276
  contactCenter := center0276
  contactBall := contact0276
  work := work0276
  center_sq := center_sq0276
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0276.1
  jac_ok := checks0276.2.1
  accepted := checks0276.2.2

def tau0277 : RatBall :=
  ⟨⟨13/80, 11/80⟩, 3/160⟩
def center0277 : GaussianRat :=
  ⟨22751869/200000000, 46647191/500000000⟩
def contact0277 : RatBall := localContactBall tau0277 center0277
def work0277 : RoundedTauEval :=
  evalTau precision tau0277 contact0277 logTwoBall

theorem center_sq0277 : (center0277.re : ℝ)^2 +
    (center0277.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0277]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0277 : work0277.theta.ok = true ∧
    work0277.jac.invOK = true ∧ acceptsUnitSq work0277.out = true := by decide +kernel

def cell0277 : CellCertificate where
  tauBall := tau0277
  contactCenter := center0277
  contactBall := contact0277
  work := work0277
  center_sq := center_sq0277
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0277.1
  jac_ok := checks0277.2.1
  accepted := checks0277.2.2

def tau0278 : RatBall :=
  ⟨⟨3/16, 11/80⟩, 3/160⟩
def center0278 : GaussianRat :=
  ⟨130837509/1000000000, 92449971/1000000000⟩
def contact0278 : RatBall := localContactBall tau0278 center0278
def work0278 : RoundedTauEval :=
  evalTau precision tau0278 contact0278 logTwoBall

theorem center_sq0278 : (center0278.re : ℝ)^2 +
    (center0278.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0278]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0278 : work0278.theta.ok = true ∧
    work0278.jac.invOK = true ∧ acceptsUnitSq work0278.out = true := by decide +kernel

def cell0278 : CellCertificate where
  tauBall := tau0278
  contactCenter := center0278
  contactBall := contact0278
  work := work0278
  center_sq := center_sq0278
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0278.1
  jac_ok := checks0278.2.1
  accepted := checks0278.2.2

def tau0279 : RatBall :=
  ⟨⟨9/80, 13/80⟩, 3/160⟩
def center0279 : GaussianRat :=
  ⟨79781827/1000000000, 56070187/500000000⟩
def contact0279 : RatBall := localContactBall tau0279 center0279
def work0279 : RoundedTauEval :=
  evalTau precision tau0279 contact0279 logTwoBall

theorem center_sq0279 : (center0279.re : ℝ)^2 +
    (center0279.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0279]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0279 : work0279.theta.ok = true ∧
    work0279.jac.invOK = true ∧ acceptsUnitSq work0279.out = true := by decide +kernel

def cell0279 : CellCertificate where
  tauBall := tau0279
  contactCenter := center0279
  contactBall := contact0279
  work := work0279
  center_sq := center_sq0279
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0279.1
  jac_ok := checks0279.2.1
  accepted := checks0279.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034


