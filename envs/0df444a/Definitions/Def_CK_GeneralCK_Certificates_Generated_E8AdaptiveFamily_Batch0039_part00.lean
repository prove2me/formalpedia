-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0039_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0039_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:17:01.047052+00:00
-- url     : https://prove2.me/theorems/b53cbdb6-2116-48b3-a38b-b76a91d640b1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0039 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0312 : RatBall :=
  ⟨⟨19/80, 9/80⟩, 3/160⟩
def center0312 : GaussianRat :=
  ⟨163469111/1000000000, 36947527/500000000⟩
def contact0312 : RatBall := localContactBall tau0312 center0312
def work0312 : RoundedTauEval :=
  evalTau precision tau0312 contact0312 logTwoBall

theorem center_sq0312 : (center0312.re : ℝ)^2 +
    (center0312.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0312]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0312 : work0312.theta.ok = true ∧
    work0312.jac.invOK = true ∧ acceptsUnitSq work0312.out = true := by decide +kernel

def cell0312 : CellCertificate where
  tauBall := tau0312
  contactCenter := center0312
  contactBall := contact0312
  work := work0312
  center_sq := center_sq0312
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0312.1
  jac_ok := checks0312.2.1
  accepted := checks0312.2.2

def tau0313 : RatBall :=
  ⟨⟨17/80, 11/80⟩, 3/160⟩
def center0313 : GaussianRat :=
  ⟨1154229/7812500, 91503559/1000000000⟩
def contact0313 : RatBall := localContactBall tau0313 center0313
def work0313 : RoundedTauEval :=
  evalTau precision tau0313 contact0313 logTwoBall

theorem center_sq0313 : (center0313.re : ℝ)^2 +
    (center0313.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0313]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0313 : work0313.theta.ok = true ∧
    work0313.jac.invOK = true ∧ acceptsUnitSq work0313.out = true := by decide +kernel

def cell0313 : CellCertificate where
  tauBall := tau0313
  contactCenter := center0313
  contactBall := contact0313
  work := work0313
  center_sq := center_sq0313
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0313.1
  jac_ok := checks0313.2.1
  accepted := checks0313.2.2

def tau0314 : RatBall :=
  ⟨⟨19/80, 11/80⟩, 3/160⟩
def center0314 : GaussianRat :=
  ⟨82225973/500000000, 18092371/200000000⟩
def contact0314 : RatBall := localContactBall tau0314 center0314
def work0314 : RoundedTauEval :=
  evalTau precision tau0314 contact0314 logTwoBall

theorem center_sq0314 : (center0314.re : ℝ)^2 +
    (center0314.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0314]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0314 : work0314.theta.ok = true ∧
    work0314.jac.invOK = true ∧ acceptsUnitSq work0314.out = true := by decide +kernel

def cell0314 : CellCertificate where
  tauBall := tau0314
  contactCenter := center0314
  contactBall := contact0314
  work := work0314
  center_sq := center_sq0314
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0314.1
  jac_ok := checks0314.2.1
  accepted := checks0314.2.2

def tau0315 : RatBall :=
  ⟨⟨21/80, 9/80⟩, 3/160⟩
def center0315 : GaussianRat :=
  ⟨44973153/250000000, 72980409/1000000000⟩
def contact0315 : RatBall := localContactBall tau0315 center0315
def work0315 : RoundedTauEval :=
  evalTau precision tau0315 contact0315 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039


