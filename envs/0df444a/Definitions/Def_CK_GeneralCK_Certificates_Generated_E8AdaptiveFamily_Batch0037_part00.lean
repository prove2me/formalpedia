-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0037_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0037_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:39:33.23132+00:00
-- url     : https://prove2.me/theorems/a131c05a-b358-41a7-a6fa-c8f2b1bbaca3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0037 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0296 : RatBall :=
  ⟨⟨23/80, 1/16⟩, 3/160⟩
def center0296 : GaussianRat :=
  ⟨194534387/1000000000, 7984577/200000000⟩
def contact0296 : RatBall := localContactBall tau0296 center0296
def work0296 : RoundedTauEval :=
  evalTau precision tau0296 contact0296 logTwoBall

theorem center_sq0296 : (center0296.re : ℝ)^2 +
    (center0296.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0296]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0296 : work0296.theta.ok = true ∧
    work0296.jac.invOK = true ∧ acceptsUnitSq work0296.out = true := by decide +kernel

def cell0296 : CellCertificate where
  tauBall := tau0296
  contactCenter := center0296
  contactBall := contact0296
  work := work0296
  center_sq := center_sq0296
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0296.1
  jac_ok := checks0296.2.1
  accepted := checks0296.2.2

def tau0297 : RatBall :=
  ⟨⟨21/80, 7/80⟩, 3/160⟩
def center0297 : GaussianRat :=
  ⟨17905297/100000000, 5669463/100000000⟩
def contact0297 : RatBall := localContactBall tau0297 center0297
def work0297 : RoundedTauEval :=
  evalTau precision tau0297 contact0297 logTwoBall

theorem center_sq0297 : (center0297.re : ℝ)^2 +
    (center0297.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0297]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0297 : work0297.theta.ok = true ∧
    work0297.jac.invOK = true ∧ acceptsUnitSq work0297.out = true := by decide +kernel

def cell0297 : CellCertificate where
  tauBall := tau0297
  contactCenter := center0297
  contactBall := contact0297
  work := work0297
  center_sq := center_sq0297
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0297.1
  jac_ok := checks0297.2.1
  accepted := checks0297.2.2

def tau0298 : RatBall :=
  ⟨⟨23/80, 7/80⟩, 3/160⟩
def center0298 : GaussianRat :=
  ⟨195201217/1000000000, 13984569/250000000⟩
def contact0298 : RatBall := localContactBall tau0298 center0298
def work0298 : RoundedTauEval :=
  evalTau precision tau0298 contact0298 logTwoBall

theorem center_sq0298 : (center0298.re : ℝ)^2 +
    (center0298.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0298]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0298 : work0298.theta.ok = true ∧
    work0298.jac.invOK = true ∧ acceptsUnitSq work0298.out = true := by decide +kernel

def cell0298 : CellCertificate where
  tauBall := tau0298
  contactCenter := center0298
  contactBall := contact0298
  work := work0298
  center_sq := center_sq0298
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0298.1
  jac_ok := checks0298.2.1
  accepted := checks0298.2.2

def tau0299 : RatBall :=
  ⟨⟨5/16, 1/80⟩, 3/160⟩
def center0299 : GaussianRat :=
  ⟨104858117/500000000, 3932321/500000000⟩
def contact0299 : RatBall := localContactBall tau0299 center0299
def work0299 : RoundedTauEval :=
  evalTau precision tau0299 contact0299 logTwoBall

theorem center_sq0299 : (center0299.re : ℝ)^2 +
    (center0299.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0299]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0299 : work0299.theta.ok = true ∧
    work0299.jac.invOK = true ∧ acceptsUnitSq work0299.out = true := by decide +kernel

def cell0299 : CellCertificate where
  tauBall := tau0299
  contactCenter := center0299
  contactBall := contact0299
  work := work0299
  center_sq := center_sq0299
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0299.1
  jac_ok := checks0299.2.1
  accepted := checks0299.2.2

def tau0300 : RatBall :=
  ⟨⟨27/80, 1/80⟩, 3/160⟩
def center0300 : GaussianRat :=
  ⟨45065623/200000000, 7745371/1000000000⟩
def contact0300 : RatBall := localContactBall tau0300 center0300
def work0300 : RoundedTauEval :=
  evalTau precision tau0300 contact0300 logTwoBall

theorem center_sq0300 : (center0300.re : ℝ)^2 +
    (center0300.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0300]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0300 : work0300.theta.ok = true ∧
    work0300.jac.invOK = true ∧ acceptsUnitSq work0300.out = true := by decide +kernel

def cell0300 : CellCertificate where
  tauBall := tau0300
  contactCenter := center0300
  contactBall := contact0300
  work := work0300
  center_sq := center_sq0300
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0300.1
  jac_ok := checks0300.2.1
  accepted := checks0300.2.2

def tau0301 : RatBall :=
  ⟨⟨5/16, 3/80⟩, 3/160⟩
def center0301 : GaussianRat :=
  ⟨209949283/1000000000, 11799931/500000000⟩
def contact0301 : RatBall := localContactBall tau0301 center0301
def work0301 : RoundedTauEval :=
  evalTau precision tau0301 contact0301 logTwoBall

theorem center_sq0301 : (center0301.re : ℝ)^2 +
    (center0301.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0301]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0301 : work0301.theta.ok = true ∧
    work0301.jac.invOK = true ∧ acceptsUnitSq work0301.out = true := by decide +kernel

def cell0301 : CellCertificate where
  tauBall := tau0301
  contactCenter := center0301
  contactBall := contact0301
  work := work0301
  center_sq := center_sq0301
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0301.1
  jac_ok := checks0301.2.1
  accepted := checks0301.2.2

def tau0302 : RatBall :=
  ⟨⟨27/80, 3/80⟩, 3/160⟩
def center0302 : GaussianRat :=
  ⟨225572371/1000000000, 4648277/200000000⟩
def contact0302 : RatBall := localContactBall tau0302 center0302
def work0302 : RoundedTauEval :=
  evalTau precision tau0302 contact0302 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037


