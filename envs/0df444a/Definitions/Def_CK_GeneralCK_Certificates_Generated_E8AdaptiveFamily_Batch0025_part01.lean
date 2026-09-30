-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0025_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0025_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:31:38.221395+00:00
-- url     : https://prove2.me/theorems/ee2350cb-1186-405c-baf1-8f84b03d7b7d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0025 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0025_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0203 : RatBall :=
  ⟨⟨-27/80, 3/80⟩, 3/160⟩
def center0203 : GaussianRat :=
  ⟨-225572371/1000000000, 4648277/200000000⟩
def contact0203 : RatBall := localContactBall tau0203 center0203
def work0203 : RoundedTauEval :=
  evalTau precision tau0203 contact0203 logTwoBall

theorem center_sq0203 : (center0203.re : ℝ)^2 +
    (center0203.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0203]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0203 : work0203.theta.ok = true ∧
    work0203.jac.invOK = true ∧ acceptsUnitSq work0203.out = true := by decide +kernel

def cell0203 : CellCertificate where
  tauBall := tau0203
  contactCenter := center0203
  contactBall := contact0203
  work := work0203
  center_sq := center_sq0203
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0203.1
  jac_ok := checks0203.2.1
  accepted := checks0203.2.2

def tau0204 : RatBall :=
  ⟨⟨-5/16, 3/80⟩, 3/160⟩
def center0204 : GaussianRat :=
  ⟨-209949283/1000000000, 11799931/500000000⟩
def contact0204 : RatBall := localContactBall tau0204 center0204
def work0204 : RoundedTauEval :=
  evalTau precision tau0204 contact0204 logTwoBall

theorem center_sq0204 : (center0204.re : ℝ)^2 +
    (center0204.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0204]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0204 : work0204.theta.ok = true ∧
    work0204.jac.invOK = true ∧ acceptsUnitSq work0204.out = true := by decide +kernel

def cell0204 : CellCertificate where
  tauBall := tau0204
  contactCenter := center0204
  contactBall := contact0204
  work := work0204
  center_sq := center_sq0204
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0204.1
  jac_ok := checks0204.2.1
  accepted := checks0204.2.2

def tau0205 : RatBall :=
  ⟨⟨-29/80, 1/16⟩, 3/160⟩
def center0205 : GaussianRat :=
  ⟨-241459683/1000000000, 9531797/250000000⟩
def contact0205 : RatBall := localContactBall tau0205 center0205
def work0205 : RoundedTauEval :=
  evalTau precision tau0205 contact0205 logTwoBall

theorem center_sq0205 : (center0205.re : ℝ)^2 +
    (center0205.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0205]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0205 : work0205.theta.ok = true ∧
    work0205.jac.invOK = true ∧ acceptsUnitSq work0205.out = true := by decide +kernel

def cell0205 : CellCertificate where
  tauBall := tau0205
  contactCenter := center0205
  contactBall := contact0205
  work := work0205
  center_sq := center_sq0205
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0205.1
  jac_ok := checks0205.2.1
  accepted := checks0205.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025


