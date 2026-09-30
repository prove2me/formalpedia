-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0014_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0014_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:20:58.375829+00:00
-- url     : https://prove2.me/theorems/473b3a93-7780-4f34-8158-ded52dfb2e28
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0014 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0112 : RatBall :=
  ⟨⟨-13/80, -13/80⟩, 3/160⟩
def center0112 : GaussianRat :=
  ⟨-114628827/1000000000, -110510723/1000000000⟩
def contact0112 : RatBall := localContactBall tau0112 center0112
def work0112 : RoundedTauEval :=
  evalTau precision tau0112 contact0112 logTwoBall

theorem center_sq0112 : (center0112.re : ℝ)^2 +
    (center0112.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0112]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0112 : work0112.theta.ok = true ∧
    work0112.jac.invOK = true ∧ acceptsUnitSq work0112.out = true := by decide +kernel

def cell0112 : CellCertificate where
  tauBall := tau0112
  contactCenter := center0112
  contactBall := contact0112
  work := work0112
  center_sq := center_sq0112
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0112.1
  jac_ok := checks0112.2.1
  accepted := checks0112.2.2

def tau0113 : RatBall :=
  ⟨⟨-11/80, -3/16⟩, 3/160⟩
def center0113 : GaussianRat :=
  ⟨-1227011/12500000, -8055803/62500000⟩
def contact0113 : RatBall := localContactBall tau0113 center0113
def work0113 : RoundedTauEval :=
  evalTau precision tau0113 contact0113 logTwoBall

theorem center_sq0113 : (center0113.re : ℝ)^2 +
    (center0113.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0113]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0113 : work0113.theta.ok = true ∧
    work0113.jac.invOK = true ∧ acceptsUnitSq work0113.out = true := by decide +kernel

def cell0113 : CellCertificate where
  tauBall := tau0113
  contactCenter := center0113
  contactBall := contact0113
  work := work0113
  center_sq := center_sq0113
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0113.1
  jac_ok := checks0113.2.1
  accepted := checks0113.2.2

def tau0114 : RatBall :=
  ⟨⟨-9/80, -3/16⟩, 3/160⟩
def center0114 : GaussianRat :=
  ⟨-80517041/1000000000, -8110609/62500000⟩
def contact0114 : RatBall := localContactBall tau0114 center0114
def work0114 : RoundedTauEval :=
  evalTau precision tau0114 contact0114 logTwoBall

theorem center_sq0114 : (center0114.re : ℝ)^2 +
    (center0114.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0114]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0114 : work0114.theta.ok = true ∧
    work0114.jac.invOK = true ∧ acceptsUnitSq work0114.out = true := by decide +kernel

def cell0114 : CellCertificate where
  tauBall := tau0114
  contactCenter := center0114
  contactBall := contact0114
  work := work0114
  center_sq := center_sq0114
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0114.1
  jac_ok := checks0114.2.1
  accepted := checks0114.2.2

def tau0115 : RatBall :=
  ⟨⟨-11/80, -13/80⟩, 3/160⟩
def center0115 : GaussianRat :=
  ⟨-48637291/500000000, -111393603/1000000000⟩
def contact0115 : RatBall := localContactBall tau0115 center0115
def work0115 : RoundedTauEval :=
  evalTau precision tau0115 contact0115 logTwoBall

theorem center_sq0115 : (center0115.re : ℝ)^2 +
    (center0115.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0115]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0115 : work0115.theta.ok = true ∧
    work0115.jac.invOK = true ∧ acceptsUnitSq work0115.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014


