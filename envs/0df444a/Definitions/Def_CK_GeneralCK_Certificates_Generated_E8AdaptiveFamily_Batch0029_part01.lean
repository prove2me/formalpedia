-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0029_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0029_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:25:26.987988+00:00
-- url     : https://prove2.me/theorems/2e8199b7-bbb1-49eb-a4f4-fac20c1b059f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0029 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0029_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center0235 : GaussianRat :=
  ⟨-26005447/200000000, 37751763/500000000⟩
def contact0235 : RatBall := localContactBall tau0235 center0235
def work0235 : RoundedTauEval :=
  evalTau precision tau0235 contact0235 logTwoBall

theorem center_sq0235 : (center0235.re : ℝ)^2 +
    (center0235.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0235]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0235 : work0235.theta.ok = true ∧
    work0235.jac.invOK = true ∧ acceptsUnitSq work0235.out = true := by decide +kernel

def cell0235 : CellCertificate where
  tauBall := tau0235
  contactCenter := center0235
  contactBall := contact0235
  work := work0235
  center_sq := center_sq0235
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0235.1
  jac_ok := checks0235.2.1
  accepted := checks0235.2.2

def tau0236 : RatBall :=
  ⟨⟨-13/80, 9/80⟩, 3/160⟩
def center0236 : GaussianRat :=
  ⟨-56522129/500000000, 76186323/1000000000⟩
def contact0236 : RatBall := localContactBall tau0236 center0236
def work0236 : RoundedTauEval :=
  evalTau precision tau0236 contact0236 logTwoBall

theorem center_sq0236 : (center0236.re : ℝ)^2 +
    (center0236.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0236]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0236 : work0236.theta.ok = true ∧
    work0236.jac.invOK = true ∧ acceptsUnitSq work0236.out = true := by decide +kernel

def cell0236 : CellCertificate where
  tauBall := tau0236
  contactCenter := center0236
  contactBall := contact0236
  work := work0236
  center_sq := center_sq0236
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0236.1
  jac_ok := checks0236.2.1
  accepted := checks0236.2.2

def tau0237 : RatBall :=
  ⟨⟨-3/16, 11/80⟩, 3/160⟩
def center0237 : GaussianRat :=
  ⟨-130837509/1000000000, 92449971/1000000000⟩
def contact0237 : RatBall := localContactBall tau0237 center0237
def work0237 : RoundedTauEval :=
  evalTau precision tau0237 contact0237 logTwoBall

theorem center_sq0237 : (center0237.re : ℝ)^2 +
    (center0237.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0237]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0237 : work0237.theta.ok = true ∧
    work0237.jac.invOK = true ∧ acceptsUnitSq work0237.out = true := by decide +kernel

def cell0237 : CellCertificate where
  tauBall := tau0237
  contactCenter := center0237
  contactBall := contact0237
  work := work0237
  center_sq := center_sq0237
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0237.1
  jac_ok := checks0237.2.1
  accepted := checks0237.2.2

def tau0238 : RatBall :=
  ⟨⟨-13/80, 11/80⟩, 3/160⟩
def center0238 : GaussianRat :=
  ⟨-22751869/200000000, 46647191/500000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029


