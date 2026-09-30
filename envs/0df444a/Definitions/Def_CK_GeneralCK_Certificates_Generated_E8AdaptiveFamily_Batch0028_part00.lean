-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0028_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0028_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:09:15.511509+00:00
-- url     : https://prove2.me/theorems/028a0142-3f03-475d-9735-2f9318835531
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0028 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0224 : RatBall :=
  ⟨⟨-21/80, 9/80⟩, 3/160⟩
def center0224 : GaussianRat :=
  ⟨-44973153/250000000, 72980409/1000000000⟩
def contact0224 : RatBall := localContactBall tau0224 center0224
def work0224 : RoundedTauEval :=
  evalTau precision tau0224 contact0224 logTwoBall

theorem center_sq0224 : (center0224.re : ℝ)^2 +
    (center0224.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0224]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0224 : work0224.theta.ok = true ∧
    work0224.jac.invOK = true ∧ acceptsUnitSq work0224.out = true := by decide +kernel

def cell0224 : CellCertificate where
  tauBall := tau0224
  contactCenter := center0224
  contactBall := contact0224
  work := work0224
  center_sq := center_sq0224
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0224.1
  jac_ok := checks0224.2.1
  accepted := checks0224.2.2

def tau0225 : RatBall :=
  ⟨⟨-23/80, 11/80⟩, 3/160⟩
def center0225 : GaussianRat :=
  ⟨-19722583/100000000, 88121387/1000000000⟩
def contact0225 : RatBall := localContactBall tau0225 center0225
def work0225 : RoundedTauEval :=
  evalTau precision tau0225 contact0225 logTwoBall

theorem center_sq0225 : (center0225.re : ℝ)^2 +
    (center0225.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0225]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0225 : work0225.theta.ok = true ∧
    work0225.jac.invOK = true ∧ acceptsUnitSq work0225.out = true := by decide +kernel

def cell0225 : CellCertificate where
  tauBall := tau0225
  contactCenter := center0225
  contactBall := contact0225
  work := work0225
  center_sq := center_sq0225
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0225.1
  jac_ok := checks0225.2.1
  accepted := checks0225.2.2

def tau0226 : RatBall :=
  ⟨⟨-21/80, 11/80⟩, 3/160⟩
def center0226 : GaussianRat :=
  ⟨-90476031/500000000, 89331987/1000000000⟩
def contact0226 : RatBall := localContactBall tau0226 center0226
def work0226 : RoundedTauEval :=
  evalTau precision tau0226 contact0226 logTwoBall

theorem center_sq0226 : (center0226.re : ℝ)^2 +
    (center0226.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0226]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0226 : work0226.theta.ok = true ∧
    work0226.jac.invOK = true ∧ acceptsUnitSq work0226.out = true := by decide +kernel

def cell0226 : CellCertificate where
  tauBall := tau0226
  contactCenter := center0226
  contactBall := contact0226
  work := work0226
  center_sq := center_sq0226
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0226.1
  jac_ok := checks0226.2.1
  accepted := checks0226.2.2

def tau0227 : RatBall :=
  ⟨⟨-19/80, 9/80⟩, 3/160⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028


