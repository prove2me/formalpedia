-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0009_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0009_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:59:16.531074+00:00
-- url     : https://prove2.me/theorems/5949c500-c653-4f76-afa1-56e4e113dcc9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0009 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0072 : RatBall :=
  ⟨⟨-5/16, -9/80⟩, 3/160⟩
def center0072 : GaussianRat :=
  ⟨-106033397/500000000, -70959907/1000000000⟩
def contact0072 : RatBall := localContactBall tau0072 center0072
def work0072 : RoundedTauEval :=
  evalTau precision tau0072 contact0072 logTwoBall

theorem center_sq0072 : (center0072.re : ℝ)^2 +
    (center0072.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0072]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0072 : work0072.theta.ok = true ∧
    work0072.jac.invOK = true ∧ acceptsUnitSq work0072.out = true := by decide +kernel

def cell0072 : CellCertificate where
  tauBall := tau0072
  contactCenter := center0072
  contactBall := contact0072
  work := work0072
  center_sq := center_sq0072
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0072.1
  jac_ok := checks0072.2.1
  accepted := checks0072.2.2

def tau0073 : RatBall :=
  ⟨⟨-21/80, -13/80⟩, 3/160⟩
def center0073 : GaussianRat :=
  ⟨-4555953/25000000, -105764329/1000000000⟩
def contact0073 : RatBall := localContactBall tau0073 center0073
def work0073 : RoundedTauEval :=
  evalTau precision tau0073 contact0073 logTwoBall

theorem center_sq0073 : (center0073.re : ℝ)^2 +
    (center0073.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0073]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0073 : work0073.theta.ok = true ∧
    work0073.jac.invOK = true ∧ acceptsUnitSq work0073.out = true := by decide +kernel

def cell0073 : CellCertificate where
  tauBall := tau0073
  contactCenter := center0073
  contactBall := contact0073
  work := work0073
  center_sq := center_sq0073
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0073.1
  jac_ok := checks0073.2.1
  accepted := checks0073.2.2

def tau0074 : RatBall :=
  ⟨⟨-17/80, -3/16⟩, 3/160⟩
def center0074 : GaussianRat :=
  ⟨-150128589/1000000000, -25067823/200000000⟩
def contact0074 : RatBall := localContactBall tau0074 center0074
def work0074 : RoundedTauEval :=
  evalTau precision tau0074 contact0074 logTwoBall

theorem center_sq0074 : (center0074.re : ℝ)^2 +
    (center0074.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0074]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0074 : work0074.theta.ok = true ∧
    work0074.jac.invOK = true ∧ acceptsUnitSq work0074.out = true := by decide +kernel

def cell0074 : CellCertificate where
  tauBall := tau0074
  contactCenter := center0074
  contactBall := contact0074
  work := work0074
  center_sq := center_sq0074
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0074.1
  jac_ok := checks0074.2.1
  accepted := checks0074.2.2

def tau0075 : RatBall :=
  ⟨⟨-19/80, -13/80⟩, 3/160⟩
def center0075 : GaussianRat :=
  ⟨-41411389/250000000, -107116873/1000000000⟩
def contact0075 : RatBall := localContactBall tau0075 center0075
def work0075 : RoundedTauEval :=
  evalTau precision tau0075 contact0075 logTwoBall

theorem center_sq0075 : (center0075.re : ℝ)^2 +
    (center0075.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0075]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0075 : work0075.theta.ok = true ∧
    work0075.jac.invOK = true ∧ acceptsUnitSq work0075.out = true := by decide +kernel

def cell0075 : CellCertificate where
  tauBall := tau0075
  contactCenter := center0075
  contactBall := contact0075
  work := work0075
  center_sq := center_sq0075
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0075.1
  jac_ok := checks0075.2.1
  accepted := checks0075.2.2

def tau0076 : RatBall :=
  ⟨⟨-17/80, -13/80⟩, 3/160⟩
def center0076 : GaussianRat :=
  ⟨-148834391/1000000000, -27091123/250000000⟩
def contact0076 : RatBall := localContactBall tau0076 center0076
def work0076 : RoundedTauEval :=
  evalTau precision tau0076 contact0076 logTwoBall

theorem center_sq0076 : (center0076.re : ℝ)^2 +
    (center0076.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0076]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0076 : work0076.theta.ok = true ∧
    work0076.jac.invOK = true ∧ acceptsUnitSq work0076.out = true := by decide +kernel

def cell0076 : CellCertificate where
  tauBall := tau0076
  contactCenter := center0076
  contactBall := contact0076
  work := work0076
  center_sq := center_sq0076
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0076.1
  jac_ok := checks0076.2.1
  accepted := checks0076.2.2

def tau0077 : RatBall :=
  ⟨⟨-23/80, -11/80⟩, 3/160⟩
def center0077 : GaussianRat :=
  ⟨-19722583/100000000, -88121387/1000000000⟩
def contact0077 : RatBall := localContactBall tau0077 center0077
def work0077 : RoundedTauEval :=
  evalTau precision tau0077 contact0077 logTwoBall

theorem center_sq0077 : (center0077.re : ℝ)^2 +
    (center0077.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0077]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0077 : work0077.theta.ok = true ∧
    work0077.jac.invOK = true ∧ acceptsUnitSq work0077.out = true := by decide +kernel

def cell0077 : CellCertificate where
  tauBall := tau0077
  contactCenter := center0077
  contactBall := contact0077
  work := work0077
  center_sq := center_sq0077
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0077.1
  jac_ok := checks0077.2.1
  accepted := checks0077.2.2

def tau0078 : RatBall :=
  ⟨⟨-21/80, -11/80⟩, 3/160⟩
def center0078 : GaussianRat :=
  ⟨-90476031/500000000, -89331987/1000000000⟩
def contact0078 : RatBall := localContactBall tau0078 center0078
def work0078 : RoundedTauEval :=
  evalTau precision tau0078 contact0078 logTwoBall

theorem center_sq0078 : (center0078.re : ℝ)^2 +
    (center0078.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0078]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009


