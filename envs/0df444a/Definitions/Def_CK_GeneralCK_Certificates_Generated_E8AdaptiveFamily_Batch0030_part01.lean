-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0030_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0030_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:13:11.58693+00:00
-- url     : https://prove2.me/theorems/c3463384-d8ed-4d53-8787-3ccd7ccd833b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0030 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0030_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center0243 : GaussianRat :=
  ⟨-48637291/500000000, 111393603/1000000000⟩
def contact0243 : RatBall := localContactBall tau0243 center0243
def work0243 : RoundedTauEval :=
  evalTau precision tau0243 contact0243 logTwoBall

theorem center_sq0243 : (center0243.re : ℝ)^2 +
    (center0243.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0243]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0243 : work0243.theta.ok = true ∧
    work0243.jac.invOK = true ∧ acceptsUnitSq work0243.out = true := by decide +kernel

def cell0243 : CellCertificate where
  tauBall := tau0243
  contactCenter := center0243
  contactBall := contact0243
  work := work0243
  center_sq := center_sq0243
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0243.1
  jac_ok := checks0243.2.1
  accepted := checks0243.2.2

def tau0244 : RatBall :=
  ⟨⟨-9/80, 13/80⟩, 3/160⟩
def center0244 : GaussianRat :=
  ⟨-79781827/1000000000, 56070187/500000000⟩
def contact0244 : RatBall := localContactBall tau0244 center0244
def work0244 : RoundedTauEval :=
  evalTau precision tau0244 contact0244 logTwoBall

theorem center_sq0244 : (center0244.re : ℝ)^2 +
    (center0244.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0244]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0244 : work0244.theta.ok = true ∧
    work0244.jac.invOK = true ∧ acceptsUnitSq work0244.out = true := by decide +kernel

def cell0244 : CellCertificate where
  tauBall := tau0244
  contactCenter := center0244
  contactBall := contact0244
  work := work0244
  center_sq := center_sq0244
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0244.1
  jac_ok := checks0244.2.1
  accepted := checks0244.2.2

def tau0245 : RatBall :=
  ⟨⟨-11/80, 3/16⟩, 3/160⟩
def center0245 : GaussianRat :=
  ⟨-1227011/12500000, 8055803/62500000⟩
def contact0245 : RatBall := localContactBall tau0245 center0245
def work0245 : RoundedTauEval :=
  evalTau precision tau0245 contact0245 logTwoBall

theorem center_sq0245 : (center0245.re : ℝ)^2 +
    (center0245.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0245]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0245 : work0245.theta.ok = true ∧
    work0245.jac.invOK = true ∧ acceptsUnitSq work0245.out = true := by decide +kernel

def cell0245 : CellCertificate where
  tauBall := tau0245
  contactCenter := center0245
  contactBall := contact0245
  work := work0245
  center_sq := center_sq0245
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0245.1
  jac_ok := checks0245.2.1
  accepted := checks0245.2.2

def tau0246 : RatBall :=
  ⟨⟨-9/80, 3/16⟩, 3/160⟩
def center0246 : GaussianRat :=
  ⟨-80517041/1000000000, 8110609/62500000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030


