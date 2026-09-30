-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0034_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0034_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:11:20.83033+00:00
-- url     : https://prove2.me/theorems/da28ba41-2112-488c-8ce7-0a4826de1d31
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0034 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0272 : RatBall :=
  ⟨⟨7/80, 13/80⟩, 3/160⟩
def center0272 : GaussianRat :=
  ⟨31086987/500000000, 112745169/1000000000⟩
def contact0272 : RatBall := localContactBall tau0272 center0272
def work0272 : RoundedTauEval :=
  evalTau precision tau0272 contact0272 logTwoBall

theorem center_sq0272 : (center0272.re : ℝ)^2 +
    (center0272.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0272]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0272 : work0272.theta.ok = true ∧
    work0272.jac.invOK = true ∧ acceptsUnitSq work0272.out = true := by decide +kernel

def cell0272 : CellCertificate where
  tauBall := tau0272
  contactCenter := center0272
  contactBall := contact0272
  work := work0272
  center_sq := center_sq0272
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0272.1
  jac_ok := checks0272.2.1
  accepted := checks0272.2.2

def tau0273 : RatBall :=
  ⟨⟨1/16, 3/16⟩, 3/160⟩
def center0273 : GaussianRat :=
  ⟨22445977/500000000, 131018253/1000000000⟩
def contact0273 : RatBall := localContactBall tau0273 center0273
def work0273 : RoundedTauEval :=
  evalTau precision tau0273 contact0273 logTwoBall

theorem center_sq0273 : (center0273.re : ℝ)^2 +
    (center0273.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0273]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0273 : work0273.theta.ok = true ∧
    work0273.jac.invOK = true ∧ acceptsUnitSq work0273.out = true := by decide +kernel

def cell0273 : CellCertificate where
  tauBall := tau0273
  contactCenter := center0273
  contactBall := contact0273
  work := work0273
  center_sq := center_sq0273
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0273.1
  jac_ok := checks0273.2.1
  accepted := checks0273.2.2

def tau0274 : RatBall :=
  ⟨⟨7/80, 3/16⟩, 3/160⟩
def center0274 : GaussianRat :=
  ⟨6275219/100000000, 65240079/500000000⟩
def contact0274 : RatBall := localContactBall tau0274 center0274
def work0274 : RoundedTauEval :=
  evalTau precision tau0274 contact0274 logTwoBall

theorem center_sq0274 : (center0274.re : ℝ)^2 +
    (center0274.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0274]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0274 : work0274.theta.ok = true ∧
    work0274.jac.invOK = true ∧ acceptsUnitSq work0274.out = true := by decide +kernel

def cell0274 : CellCertificate where
  tauBall := tau0274
  contactCenter := center0274
  contactBall := contact0274
  work := work0274
  center_sq := center_sq0274
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0274.1
  jac_ok := checks0274.2.1
  accepted := checks0274.2.2

def tau0275 : RatBall :=
  ⟨⟨13/80, 9/80⟩, 3/160⟩
def center0275 : GaussianRat :=
  ⟨56522129/500000000, 76186323/1000000000⟩
def contact0275 : RatBall := localContactBall tau0275 center0275
def work0275 : RoundedTauEval :=
  evalTau precision tau0275 contact0275 logTwoBall

theorem center_sq0275 : (center0275.re : ℝ)^2 +
    (center0275.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0275]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0275 : work0275.theta.ok = true ∧
    work0275.jac.invOK = true ∧ acceptsUnitSq work0275.out = true := by decide +kernel

def cell0275 : CellCertificate where
  tauBall := tau0275
  contactCenter := center0275
  contactBall := contact0275
  work := work0275
  center_sq := center_sq0275
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0275.1
  jac_ok := checks0275.2.1
  accepted := checks0275.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034


