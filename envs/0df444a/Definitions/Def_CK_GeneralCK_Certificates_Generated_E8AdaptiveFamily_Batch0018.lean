-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0018
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0018
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:44:15.683385+00:00
-- url     : https://prove2.me/theorems/6782921c-11e7-460c-8447-d69a1bfd8d2e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0018` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0018` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0018` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0018 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0018.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0018 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0018

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0144 : RatBall :=
  ⟨⟨3/16, -17/80⟩, 3/160⟩
def center0144 : GaussianRat :=
  ⟨16793263/125000000, -143981719/1000000000⟩
def contact0144 : RatBall := localContactBall tau0144 center0144
def work0144 : RoundedTauEval :=
  evalTau precision tau0144 contact0144 logTwoBall

theorem center_sq0144 : (center0144.re : ℝ)^2 +
    (center0144.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0144]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0144 : work0144.theta.ok = true ∧
    work0144.jac.invOK = true ∧ acceptsUnitSq work0144.out = true := by decide +kernel

def cell0144 : CellCertificate where
  tauBall := tau0144
  contactCenter := center0144
  contactBall := contact0144
  work := work0144
  center_sq := center_sq0144
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0144.1
  jac_ok := checks0144.2.1
  accepted := checks0144.2.2

def tau0145 : RatBall :=
  ⟨⟨1/16, -3/16⟩, 3/160⟩
def center0145 : GaussianRat :=
  ⟨22445977/500000000, -131018253/1000000000⟩
def contact0145 : RatBall := localContactBall tau0145 center0145
def work0145 : RoundedTauEval :=
  evalTau precision tau0145 contact0145 logTwoBall

theorem center_sq0145 : (center0145.re : ℝ)^2 +
    (center0145.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0145]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0145 : work0145.theta.ok = true ∧
    work0145.jac.invOK = true ∧ acceptsUnitSq work0145.out = true := by decide +kernel

def cell0145 : CellCertificate where
  tauBall := tau0145
  contactCenter := center0145
  contactBall := contact0145
  work := work0145
  center_sq := center_sq0145
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0145.1
  jac_ok := checks0145.2.1
  accepted := checks0145.2.2

def tau0146 : RatBall :=
  ⟨⟨7/80, -3/16⟩, 3/160⟩
def center0146 : GaussianRat :=
  ⟨6275219/100000000, -65240079/500000000⟩
def contact0146 : RatBall := localContactBall tau0146 center0146
def work0146 : RoundedTauEval :=
  evalTau precision tau0146 contact0146 logTwoBall

theorem center_sq0146 : (center0146.re : ℝ)^2 +
    (center0146.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0146]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0146 : work0146.theta.ok = true ∧
    work0146.jac.invOK = true ∧ acceptsUnitSq work0146.out = true := by decide +kernel

def cell0146 : CellCertificate where
  tauBall := tau0146
  contactCenter := center0146
  contactBall := contact0146
  work := work0146
  center_sq := center_sq0146
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0146.1
  jac_ok := checks0146.2.1
  accepted := checks0146.2.2

def tau0147 : RatBall :=
  ⟨⟨1/16, -13/80⟩, 3/160⟩
def center0147 : GaussianRat :=
  ⟨44475471/1000000000, -14150393/125000000⟩
def contact0147 : RatBall := localContactBall tau0147 center0147
def work0147 : RoundedTauEval :=
  evalTau precision tau0147 contact0147 logTwoBall

theorem center_sq0147 : (center0147.re : ℝ)^2 +
    (center0147.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0147]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0147 : work0147.theta.ok = true ∧
    work0147.jac.invOK = true ∧ acceptsUnitSq work0147.out = true := by decide +kernel

def cell0147 : CellCertificate where
  tauBall := tau0147
  contactCenter := center0147
  contactBall := contact0147
  work := work0147
  center_sq := center_sq0147
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0147.1
  jac_ok := checks0147.2.1
  accepted := checks0147.2.2

def tau0148 : RatBall :=
  ⟨⟨7/80, -13/80⟩, 3/160⟩
def center0148 : GaussianRat :=
  ⟨31086987/500000000, -112745169/1000000000⟩
def contact0148 : RatBall := localContactBall tau0148 center0148
def work0148 : RoundedTauEval :=
  evalTau precision tau0148 contact0148 logTwoBall

theorem center_sq0148 : (center0148.re : ℝ)^2 +
    (center0148.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0148]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0148 : work0148.theta.ok = true ∧
    work0148.jac.invOK = true ∧ acceptsUnitSq work0148.out = true := by decide +kernel

def cell0148 : CellCertificate where
  tauBall := tau0148
  contactCenter := center0148
  contactBall := contact0148
  work := work0148
  center_sq := center_sq0148
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0148.1
  jac_ok := checks0148.2.1
  accepted := checks0148.2.2

def tau0149 : RatBall :=
  ⟨⟨9/80, -3/16⟩, 3/160⟩
def center0149 : GaussianRat :=
  ⟨80517041/1000000000, -8110609/62500000⟩
def contact0149 : RatBall := localContactBall tau0149 center0149
def work0149 : RoundedTauEval :=
  evalTau precision tau0149 contact0149 logTwoBall

theorem center_sq0149 : (center0149.re : ℝ)^2 +
    (center0149.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0149]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0149 : work0149.theta.ok = true ∧
    work0149.jac.invOK = true ∧ acceptsUnitSq work0149.out = true := by decide +kernel

def cell0149 : CellCertificate where
  tauBall := tau0149
  contactCenter := center0149
  contactBall := contact0149
  work := work0149
  center_sq := center_sq0149
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0149.1
  jac_ok := checks0149.2.1
  accepted := checks0149.2.2

def tau0150 : RatBall :=
  ⟨⟨11/80, -3/16⟩, 3/160⟩
def center0150 : GaussianRat :=
  ⟨1227011/12500000, -8055803/62500000⟩
def contact0150 : RatBall := localContactBall tau0150 center0150
def work0150 : RoundedTauEval :=
  evalTau precision tau0150 contact0150 logTwoBall

theorem center_sq0150 : (center0150.re : ℝ)^2 +
    (center0150.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0150]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0150 : work0150.theta.ok = true ∧
    work0150.jac.invOK = true ∧ acceptsUnitSq work0150.out = true := by decide +kernel

def cell0150 : CellCertificate where
  tauBall := tau0150
  contactCenter := center0150
  contactBall := contact0150
  work := work0150
  center_sq := center_sq0150
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0150.1
  jac_ok := checks0150.2.1
  accepted := checks0150.2.2

def tau0151 : RatBall :=
  ⟨⟨9/80, -13/80⟩, 3/160⟩
def center0151 : GaussianRat :=
  ⟨79781827/1000000000, -56070187/500000000⟩
def contact0151 : RatBall := localContactBall tau0151 center0151
def work0151 : RoundedTauEval :=
  evalTau precision tau0151 contact0151 logTwoBall

theorem center_sq0151 : (center0151.re : ℝ)^2 +
    (center0151.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0151]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0151 : work0151.theta.ok = true ∧
    work0151.jac.invOK = true ∧ acceptsUnitSq work0151.out = true := by decide +kernel

def cell0151 : CellCertificate where
  tauBall := tau0151
  contactCenter := center0151
  contactBall := contact0151
  work := work0151
  center_sq := center_sq0151
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0151.1
  jac_ok := checks0151.2.1
  accepted := checks0151.2.2

def cells : List CellCertificate := [cell0144, cell0145, cell0146, cell0147, cell0148, cell0149, cell0150, cell0151]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0018

end


