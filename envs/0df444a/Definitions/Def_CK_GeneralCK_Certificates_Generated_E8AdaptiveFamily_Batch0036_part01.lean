-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0036_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0036_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:55:56.269068+00:00
-- url     : https://prove2.me/theorems/89688d46-b6bd-4ce0-ae99-3b5be578fa09
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0036 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0036_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0291 : RatBall :=
  ⟨⟨17/80, 1/16⟩, 3/160⟩
def center0291 : GaussianRat :=
  ⟨29119789/200000000, 10355411/250000000⟩
def contact0291 : RatBall := localContactBall tau0291 center0291
def work0291 : RoundedTauEval :=
  evalTau precision tau0291 contact0291 logTwoBall

theorem center_sq0291 : (center0291.re : ℝ)^2 +
    (center0291.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0291]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0291 : work0291.theta.ok = true ∧
    work0291.jac.invOK = true ∧ acceptsUnitSq work0291.out = true := by decide +kernel

def cell0291 : CellCertificate where
  tauBall := tau0291
  contactCenter := center0291
  contactBall := contact0291
  work := work0291
  center_sq := center_sq0291
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0291.1
  jac_ok := checks0291.2.1
  accepted := checks0291.2.2

def tau0292 : RatBall :=
  ⟨⟨19/80, 1/16⟩, 3/160⟩
def center0292 : GaussianRat :=
  ⟨81055451/500000000, 40960501/1000000000⟩
def contact0292 : RatBall := localContactBall tau0292 center0292
def work0292 : RoundedTauEval :=
  evalTau precision tau0292 contact0292 logTwoBall

theorem center_sq0292 : (center0292.re : ℝ)^2 +
    (center0292.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0292]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0292 : work0292.theta.ok = true ∧
    work0292.jac.invOK = true ∧ acceptsUnitSq work0292.out = true := by decide +kernel

def cell0292 : CellCertificate where
  tauBall := tau0292
  contactCenter := center0292
  contactBall := contact0292
  work := work0292
  center_sq := center_sq0292
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0292.1
  jac_ok := checks0292.2.1
  accepted := checks0292.2.2

def tau0293 : RatBall :=
  ⟨⟨17/80, 7/80⟩, 3/160⟩
def center0293 : GaussianRat :=
  ⟨146129149/1000000000, 3628117/62500000⟩
def contact0293 : RatBall := localContactBall tau0293 center0293
def work0293 : RoundedTauEval :=
  evalTau precision tau0293 contact0293 logTwoBall

theorem center_sq0293 : (center0293.re : ℝ)^2 +
    (center0293.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0293]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0293 : work0293.theta.ok = true ∧
    work0293.jac.invOK = true ∧ acceptsUnitSq work0293.out = true := by decide +kernel

def cell0293 : CellCertificate where
  tauBall := tau0293
  contactCenter := center0293
  contactBall := contact0293
  work := work0293
  center_sq := center_sq0293
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0293.1
  jac_ok := checks0293.2.1
  accepted := checks0293.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036


