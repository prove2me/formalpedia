-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0021_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0021_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:09:33.384456+00:00
-- url     : https://prove2.me/theorems/84cb2db1-71f7-4f5a-8107-a36ab49b5ebf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0021 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0168 : RatBall :=
  ⟨⟨19/80, -9/80⟩, 3/160⟩
def center0168 : GaussianRat :=
  ⟨163469111/1000000000, -36947527/500000000⟩
def contact0168 : RatBall := localContactBall tau0168 center0168
def work0168 : RoundedTauEval :=
  evalTau precision tau0168 contact0168 logTwoBall

theorem center_sq0168 : (center0168.re : ℝ)^2 +
    (center0168.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0168]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0168 : work0168.theta.ok = true ∧
    work0168.jac.invOK = true ∧ acceptsUnitSq work0168.out = true := by decide +kernel

def cell0168 : CellCertificate where
  tauBall := tau0168
  contactCenter := center0168
  contactBall := contact0168
  work := work0168
  center_sq := center_sq0168
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0168.1
  jac_ok := checks0168.2.1
  accepted := checks0168.2.2

def tau0169 : RatBall :=
  ⟨⟨21/80, -11/80⟩, 3/160⟩
def center0169 : GaussianRat :=
  ⟨90476031/500000000, -89331987/1000000000⟩
def contact0169 : RatBall := localContactBall tau0169 center0169
def work0169 : RoundedTauEval :=
  evalTau precision tau0169 contact0169 logTwoBall

theorem center_sq0169 : (center0169.re : ℝ)^2 +
    (center0169.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0169]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0169 : work0169.theta.ok = true ∧
    work0169.jac.invOK = true ∧ acceptsUnitSq work0169.out = true := by decide +kernel

def cell0169 : CellCertificate where
  tauBall := tau0169
  contactCenter := center0169
  contactBall := contact0169
  work := work0169
  center_sq := center_sq0169
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0169.1
  jac_ok := checks0169.2.1
  accepted := checks0169.2.2

def tau0170 : RatBall :=
  ⟨⟨23/80, -11/80⟩, 3/160⟩
def center0170 : GaussianRat :=
  ⟨19722583/100000000, -88121387/1000000000⟩
def contact0170 : RatBall := localContactBall tau0170 center0170
def work0170 : RoundedTauEval :=
  evalTau precision tau0170 contact0170 logTwoBall

theorem center_sq0170 : (center0170.re : ℝ)^2 +
    (center0170.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0170]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0170 : work0170.theta.ok = true ∧
    work0170.jac.invOK = true ∧ acceptsUnitSq work0170.out = true := by decide +kernel

def cell0170 : CellCertificate where
  tauBall := tau0170
  contactCenter := center0170
  contactBall := contact0170
  work := work0170
  center_sq := center_sq0170
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0170.1
  jac_ok := checks0170.2.1
  accepted := checks0170.2.2

def tau0171 : RatBall :=
  ⟨⟨21/80, -9/80⟩, 3/160⟩
def center0171 : GaussianRat :=
  ⟨44973153/250000000, -72980409/1000000000⟩
def contact0171 : RatBall := localContactBall tau0171 center0171
def work0171 : RoundedTauEval :=
  evalTau precision tau0171 contact0171 logTwoBall

theorem center_sq0171 : (center0171.re : ℝ)^2 +
    (center0171.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0171]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0171 : work0171.theta.ok = true ∧
    work0171.jac.invOK = true ∧ acceptsUnitSq work0171.out = true := by decide +kernel

def cell0171 : CellCertificate where
  tauBall := tau0171
  contactCenter := center0171
  contactBall := contact0171
  work := work0171
  center_sq := center_sq0171
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0171.1
  jac_ok := checks0171.2.1
  accepted := checks0171.2.2

def tau0172 : RatBall :=
  ⟨⟨23/80, -9/80⟩, 3/160⟩
def center0172 : GaussianRat :=
  ⟨196096551/1000000000, -71999991/1000000000⟩
def contact0172 : RatBall := localContactBall tau0172 center0172
def work0172 : RoundedTauEval :=
  evalTau precision tau0172 contact0172 logTwoBall

theorem center_sq0172 : (center0172.re : ℝ)^2 +
    (center0172.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0172]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021


