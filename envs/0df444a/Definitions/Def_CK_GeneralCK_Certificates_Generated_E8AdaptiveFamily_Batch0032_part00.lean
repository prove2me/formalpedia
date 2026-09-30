-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0032_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0032_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:12:55.479393+00:00
-- url     : https://prove2.me/theorems/f2fd19b4-9042-4d5d-8383-14eb9ef5cfec
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0032 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0256 : RatBall :=
  ⟨⟨-9/80, 19/80⟩, 3/160⟩
def center0256 : GaussianRat :=
  ⟨-20589547/250000000, 33110861/200000000⟩
def contact0256 : RatBall := localContactBall tau0256 center0256
def work0256 : RoundedTauEval :=
  evalTau precision tau0256 contact0256 logTwoBall

theorem center_sq0256 : (center0256.re : ℝ)^2 +
    (center0256.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0256]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0256 : work0256.theta.ok = true ∧
    work0256.jac.invOK = true ∧ acceptsUnitSq work0256.out = true := by decide +kernel

def cell0256 : CellCertificate where
  tauBall := tau0256
  contactCenter := center0256
  contactBall := contact0256
  work := work0256
  center_sq := center_sq0256
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0256.1
  jac_ok := checks0256.2.1
  accepted := checks0256.2.2

def tau0257 : RatBall :=
  ⟨⟨-7/80, 17/80⟩, 3/160⟩
def center0257 : GaussianRat :=
  ⟨-31712973/500000000, 37096923/250000000⟩
def contact0257 : RatBall := localContactBall tau0257 center0257
def work0257 : RoundedTauEval :=
  evalTau precision tau0257 contact0257 logTwoBall

theorem center_sq0257 : (center0257.re : ℝ)^2 +
    (center0257.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0257]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0257 : work0257.theta.ok = true ∧
    work0257.jac.invOK = true ∧ acceptsUnitSq work0257.out = true := by decide +kernel

def cell0257 : CellCertificate where
  tauBall := tau0257
  contactCenter := center0257
  contactBall := contact0257
  work := work0257
  center_sq := center_sq0257
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0257.1
  jac_ok := checks0257.2.1
  accepted := checks0257.2.2

def tau0258 : RatBall :=
  ⟨⟨-1/16, 17/80⟩, 3/160⟩
def center0258 : GaussianRat :=
  ⟨-22688687/500000000, 149010417/1000000000⟩
def contact0258 : RatBall := localContactBall tau0258 center0258
def work0258 : RoundedTauEval :=
  evalTau precision tau0258 contact0258 logTwoBall

theorem center_sq0258 : (center0258.re : ℝ)^2 +
    (center0258.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0258]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0258 : work0258.theta.ok = true ∧
    work0258.jac.invOK = true ∧ acceptsUnitSq work0258.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032


