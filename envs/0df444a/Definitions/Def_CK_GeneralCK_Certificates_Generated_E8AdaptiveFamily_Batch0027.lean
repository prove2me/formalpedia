-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0027
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0027
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:47:58.282044+00:00
-- url     : https://prove2.me/theorems/3867439a-9279-49e9-afd7-5b16596de844
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0027.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0027_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0220 : work0220.theta.ok = true ∧
    work0220.jac.invOK = true ∧ acceptsUnitSq work0220.out = true := by decide +kernel

def cell0220 : CellCertificate where
  tauBall := tau0220
  contactCenter := center0220
  contactBall := contact0220
  work := work0220
  center_sq := center_sq0220
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0220.1
  jac_ok := checks0220.2.1
  accepted := checks0220.2.2

def tau0221 : RatBall :=
  ⟨⟨-17/80, 7/80⟩, 3/160⟩
def center0221 : GaussianRat :=
  ⟨-146129149/1000000000, 3628117/62500000⟩
def contact0221 : RatBall := localContactBall tau0221 center0221
def work0221 : RoundedTauEval :=
  evalTau precision tau0221 contact0221 logTwoBall

theorem center_sq0221 : (center0221.re : ℝ)^2 +
    (center0221.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0221]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0221 : work0221.theta.ok = true ∧
    work0221.jac.invOK = true ∧ acceptsUnitSq work0221.out = true := by decide +kernel

def cell0221 : CellCertificate where
  tauBall := tau0221
  contactCenter := center0221
  contactBall := contact0221
  work := work0221
  center_sq := center_sq0221
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0221.1
  jac_ok := checks0221.2.1
  accepted := checks0221.2.2

def tau0222 : RatBall :=
  ⟨⟨-5/16, 9/80⟩, 3/160⟩
def center0222 : GaussianRat :=
  ⟨-106033397/500000000, 70959907/1000000000⟩
def contact0222 : RatBall := localContactBall tau0222 center0222
def work0222 : RoundedTauEval :=
  evalTau precision tau0222 contact0222 logTwoBall

theorem center_sq0222 : (center0222.re : ℝ)^2 +
    (center0222.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0222]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0222 : work0222.theta.ok = true ∧
    work0222.jac.invOK = true ∧ acceptsUnitSq work0222.out = true := by decide +kernel

def cell0222 : CellCertificate where
  tauBall := tau0222
  contactCenter := center0222
  contactBall := contact0222
  work := work0222
  center_sq := center_sq0222
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0222.1
  jac_ok := checks0222.2.1
  accepted := checks0222.2.2

def tau0223 : RatBall :=
  ⟨⟨-23/80, 9/80⟩, 3/160⟩
def center0223 : GaussianRat :=
  ⟨-196096551/1000000000, 71999991/1000000000⟩
def contact0223 : RatBall := localContactBall tau0223 center0223
def work0223 : RoundedTauEval :=
  evalTau precision tau0223 contact0223 logTwoBall

theorem center_sq0223 : (center0223.re : ℝ)^2 +
    (center0223.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0223]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0223 : work0223.theta.ok = true ∧
    work0223.jac.invOK = true ∧ acceptsUnitSq work0223.out = true := by decide +kernel

def cell0223 : CellCertificate where
  tauBall := tau0223
  contactCenter := center0223
  contactBall := contact0223
  work := work0223
  center_sq := center_sq0223
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0223.1
  jac_ok := checks0223.2.1
  accepted := checks0223.2.2

def cells : List CellCertificate := [cell0216, cell0217, cell0218, cell0219, cell0220, cell0221, cell0222, cell0223]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027


