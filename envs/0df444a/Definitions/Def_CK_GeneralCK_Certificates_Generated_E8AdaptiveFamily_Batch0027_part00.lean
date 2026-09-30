-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0027_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0027_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:21:00.504695+00:00
-- url     : https://prove2.me/theorems/49b4efd2-03d8-452c-8265-34e04ec0c6c4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0027 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0216 : RatBall :=
  ⟨⟨-23/80, 7/80⟩, 3/160⟩
def center0216 : GaussianRat :=
  ⟨-195201217/1000000000, 13984569/250000000⟩
def contact0216 : RatBall := localContactBall tau0216 center0216
def work0216 : RoundedTauEval :=
  evalTau precision tau0216 contact0216 logTwoBall

theorem center_sq0216 : (center0216.re : ℝ)^2 +
    (center0216.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0216]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0216 : work0216.theta.ok = true ∧
    work0216.jac.invOK = true ∧ acceptsUnitSq work0216.out = true := by decide +kernel

def cell0216 : CellCertificate where
  tauBall := tau0216
  contactCenter := center0216
  contactBall := contact0216
  work := work0216
  center_sq := center_sq0216
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0216.1
  jac_ok := checks0216.2.1
  accepted := checks0216.2.2

def tau0217 : RatBall :=
  ⟨⟨-21/80, 7/80⟩, 3/160⟩
def center0217 : GaussianRat :=
  ⟨-17905297/100000000, 5669463/100000000⟩
def contact0217 : RatBall := localContactBall tau0217 center0217
def work0217 : RoundedTauEval :=
  evalTau precision tau0217 contact0217 logTwoBall

theorem center_sq0217 : (center0217.re : ℝ)^2 +
    (center0217.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0217]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0217 : work0217.theta.ok = true ∧
    work0217.jac.invOK = true ∧ acceptsUnitSq work0217.out = true := by decide +kernel

def cell0217 : CellCertificate where
  tauBall := tau0217
  contactCenter := center0217
  contactBall := contact0217
  work := work0217
  center_sq := center_sq0217
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0217.1
  jac_ok := checks0217.2.1
  accepted := checks0217.2.2

def tau0218 : RatBall :=
  ⟨⟨-19/80, 1/16⟩, 3/160⟩
def center0218 : GaussianRat :=
  ⟨-81055451/500000000, 40960501/1000000000⟩
def contact0218 : RatBall := localContactBall tau0218 center0218
def work0218 : RoundedTauEval :=
  evalTau precision tau0218 contact0218 logTwoBall

theorem center_sq0218 : (center0218.re : ℝ)^2 +
    (center0218.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0218]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0218 : work0218.theta.ok = true ∧
    work0218.jac.invOK = true ∧ acceptsUnitSq work0218.out = true := by decide +kernel

def cell0218 : CellCertificate where
  tauBall := tau0218
  contactCenter := center0218
  contactBall := contact0218
  work := work0218
  center_sq := center_sq0218
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0218.1
  jac_ok := checks0218.2.1
  accepted := checks0218.2.2

def tau0219 : RatBall :=
  ⟨⟨-17/80, 1/16⟩, 3/160⟩
def center0219 : GaussianRat :=
  ⟨-29119789/200000000, 10355411/250000000⟩
def contact0219 : RatBall := localContactBall tau0219 center0219
def work0219 : RoundedTauEval :=
  evalTau precision tau0219 contact0219 logTwoBall

theorem center_sq0219 : (center0219.re : ℝ)^2 +
    (center0219.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0219]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0219 : work0219.theta.ok = true ∧
    work0219.jac.invOK = true ∧ acceptsUnitSq work0219.out = true := by decide +kernel

def cell0219 : CellCertificate where
  tauBall := tau0219
  contactCenter := center0219
  contactBall := contact0219
  work := work0219
  center_sq := center_sq0219
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0219.1
  jac_ok := checks0219.2.1
  accepted := checks0219.2.2

def tau0220 : RatBall :=
  ⟨⟨-19/80, 7/80⟩, 3/160⟩
def center0220 : GaussianRat :=
  ⟨-162690477/1000000000, 28700003/500000000⟩
def contact0220 : RatBall := localContactBall tau0220 center0220
def work0220 : RoundedTauEval :=
  evalTau precision tau0220 contact0220 logTwoBall

theorem center_sq0220 : (center0220.re : ℝ)^2 +
    (center0220.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0220]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027


