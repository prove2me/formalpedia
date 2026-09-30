-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0008_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0008_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:24:26.737575+00:00
-- url     : https://prove2.me/theorems/a36455bd-9eaf-452c-90bd-a06d88be95ff
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0008 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0008_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0067 : RatBall :=
  ⟨⟨-1/16, -17/80⟩, 3/160⟩
def center0067 : GaussianRat :=
  ⟨-22688687/500000000, -149010417/1000000000⟩
def contact0067 : RatBall := localContactBall tau0067 center0067
def work0067 : RoundedTauEval :=
  evalTau precision tau0067 contact0067 logTwoBall

theorem center_sq0067 : (center0067.re : ℝ)^2 +
    (center0067.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0067]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0067 : work0067.theta.ok = true ∧
    work0067.jac.invOK = true ∧ acceptsUnitSq work0067.out = true := by decide +kernel

def cell0067 : CellCertificate where
  tauBall := tau0067
  contactCenter := center0067
  contactBall := contact0067
  work := work0067
  center_sq := center_sq0067
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0067.1
  jac_ok := checks0067.2.1
  accepted := checks0067.2.2

def tau0068 : RatBall :=
  ⟨⟨-3/80, -19/80⟩, 3/160⟩
def center0068 : GaussianRat :=
  ⟨-551859/20000000, -167686167/1000000000⟩
def contact0068 : RatBall := localContactBall tau0068 center0068
def work0068 : RoundedTauEval :=
  evalTau precision tau0068 contact0068 logTwoBall

theorem center_sq0068 : (center0068.re : ℝ)^2 +
    (center0068.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0068]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0068 : work0068.theta.ok = true ∧
    work0068.jac.invOK = true ∧ acceptsUnitSq work0068.out = true := by decide +kernel

def cell0068 : CellCertificate where
  tauBall := tau0068
  contactCenter := center0068
  contactBall := contact0068
  work := work0068
  center_sq := center_sq0068
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0068.1
  jac_ok := checks0068.2.1
  accepted := checks0068.2.2

def tau0069 : RatBall :=
  ⟨⟨-1/80, -19/80⟩, 3/160⟩
def center0069 : GaussianRat :=
  ⟨-1150363/125000000, -41981661/250000000⟩
def contact0069 : RatBall := localContactBall tau0069 center0069
def work0069 : RoundedTauEval :=
  evalTau precision tau0069 contact0069 logTwoBall

theorem center_sq0069 : (center0069.re : ℝ)^2 +
    (center0069.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0069]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0069 : work0069.theta.ok = true ∧
    work0069.jac.invOK = true ∧ acceptsUnitSq work0069.out = true := by decide +kernel

def cell0069 : CellCertificate where
  tauBall := tau0069
  contactCenter := center0069
  contactBall := contact0069
  work := work0069
  center_sq := center_sq0069
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0069.1
  jac_ok := checks0069.2.1
  accepted := checks0069.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008


