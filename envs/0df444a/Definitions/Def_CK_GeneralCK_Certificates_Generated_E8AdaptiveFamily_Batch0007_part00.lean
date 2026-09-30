-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0007_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0007_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:33:23.549216+00:00
-- url     : https://prove2.me/theorems/dd59d0bd-900a-4a07-8cef-56af7f8fbfd8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0007 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0056 : RatBall :=
  ⟨⟨-11/80, -17/80⟩, 3/160⟩
def center0056 : GaussianRat :=
  ⟨-24798221/250000000, -36637923/250000000⟩
def contact0056 : RatBall := localContactBall tau0056 center0056
def work0056 : RoundedTauEval :=
  evalTau precision tau0056 contact0056 logTwoBall

theorem center_sq0056 : (center0056.re : ℝ)^2 +
    (center0056.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0056]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0056 : work0056.theta.ok = true ∧
    work0056.jac.invOK = true ∧ acceptsUnitSq work0056.out = true := by decide +kernel

def cell0056 : CellCertificate where
  tauBall := tau0056
  contactCenter := center0056
  contactBall := contact0056
  work := work0056
  center_sq := center_sq0056
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0056.1
  jac_ok := checks0056.2.1
  accepted := checks0056.2.2

def tau0057 : RatBall :=
  ⟨⟨-9/80, -17/80⟩, 3/160⟩
def center0057 : GaussianRat :=
  ⟨-4068673/50000000, -73782899/500000000⟩
def contact0057 : RatBall := localContactBall tau0057 center0057
def work0057 : RoundedTauEval :=
  evalTau precision tau0057 contact0057 logTwoBall

theorem center_sq0057 : (center0057.re : ℝ)^2 +
    (center0057.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0057]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0057 : work0057.theta.ok = true ∧
    work0057.jac.invOK = true ∧ acceptsUnitSq work0057.out = true := by decide +kernel

def cell0057 : CellCertificate where
  tauBall := tau0057
  contactCenter := center0057
  contactBall := contact0057
  work := work0057
  center_sq := center_sq0057
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0057.1
  jac_ok := checks0057.2.1
  accepted := checks0057.2.2

def tau0058 : RatBall :=
  ⟨⟨-7/80, -21/80⟩, 3/160⟩
def center0058 : GaussianRat :=
  ⟨-6508393/100000000, -184829567/1000000000⟩
def contact0058 : RatBall := localContactBall tau0058 center0058
def work0058 : RoundedTauEval :=
  evalTau precision tau0058 contact0058 logTwoBall

theorem center_sq0058 : (center0058.re : ℝ)^2 +
    (center0058.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0058]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0058 : work0058.theta.ok = true ∧
    work0058.jac.invOK = true ∧ acceptsUnitSq work0058.out = true := by decide +kernel

def cell0058 : CellCertificate where
  tauBall := tau0058
  contactCenter := center0058
  contactBall := contact0058
  work := work0058
  center_sq := center_sq0058
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0058.1
  jac_ok := checks0058.2.1
  accepted := checks0058.2.2

def tau0059 : RatBall :=
  ⟨⟨-1/16, -21/80⟩, 3/160⟩
def center0059 : GaussianRat :=
  ⟨-46572457/1000000000, -46409673/250000000⟩
def contact0059 : RatBall := localContactBall tau0059 center0059
def work0059 : RoundedTauEval :=
  evalTau precision tau0059 contact0059 logTwoBall

theorem center_sq0059 : (center0059.re : ℝ)^2 +
    (center0059.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0059]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0059 : work0059.theta.ok = true ∧
    work0059.jac.invOK = true ∧ acceptsUnitSq work0059.out = true := by decide +kernel

def cell0059 : CellCertificate where
  tauBall := tau0059
  contactCenter := center0059
  contactBall := contact0059
  work := work0059
  center_sq := center_sq0059
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0059.1
  jac_ok := checks0059.2.1
  accepted := checks0059.2.2

def tau0060 : RatBall :=
  ⟨⟨-3/80, -23/80⟩, 3/160⟩
def center0060 : GaussianRat :=
  ⟨-14206169/500000000, -204949543/1000000000⟩
def contact0060 : RatBall := localContactBall tau0060 center0060
def work0060 : RoundedTauEval :=
  evalTau precision tau0060 contact0060 logTwoBall

theorem center_sq0060 : (center0060.re : ℝ)^2 +
    (center0060.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0060]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0060 : work0060.theta.ok = true ∧
    work0060.jac.invOK = true ∧ acceptsUnitSq work0060.out = true := by decide +kernel

def cell0060 : CellCertificate where
  tauBall := tau0060
  contactCenter := center0060
  contactBall := contact0060
  work := work0060
  center_sq := center_sq0060
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0060.1
  jac_ok := checks0060.2.1
  accepted := checks0060.2.2

def tau0061 : RatBall :=
  ⟨⟨-1/80, -23/80⟩, 3/160⟩
def center0061 : GaussianRat :=
  ⟨-4738451/500000000, -102628961/500000000⟩
def contact0061 : RatBall := localContactBall tau0061 center0061
def work0061 : RoundedTauEval :=
  evalTau precision tau0061 contact0061 logTwoBall

theorem center_sq0061 : (center0061.re : ℝ)^2 +
    (center0061.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0061]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0061 : work0061.theta.ok = true ∧
    work0061.jac.invOK = true ∧ acceptsUnitSq work0061.out = true := by decide +kernel

def cell0061 : CellCertificate where
  tauBall := tau0061
  contactCenter := center0061
  contactBall := contact0061
  work := work0061
  center_sq := center_sq0061
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0061.1
  jac_ok := checks0061.2.1
  accepted := checks0061.2.2

def tau0062 : RatBall :=
  ⟨⟨-3/80, -21/80⟩, 3/160⟩
def center0062 : GaussianRat :=
  ⟨-27977261/1000000000, -186182371/1000000000⟩
def contact0062 : RatBall := localContactBall tau0062 center0062
def work0062 : RoundedTauEval :=
  evalTau precision tau0062 contact0062 logTwoBall

theorem center_sq0062 : (center0062.re : ℝ)^2 +
    (center0062.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0062]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007


