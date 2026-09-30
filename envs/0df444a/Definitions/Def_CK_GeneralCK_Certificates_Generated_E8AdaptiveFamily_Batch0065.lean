-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0065
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0065
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:29:54.917419+00:00
-- url     : https://prove2.me/theorems/62a5ea43-6efc-4d5e-81de-a1c218d4a1f5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0065` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0065` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0065` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0065 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0065.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0065 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0065

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0520 : RatBall :=
  ⟨⟨-51/160, -21/160⟩, 3/320⟩
def center0520 : GaussianRat :=
  ⟨-216902699/1000000000, -20636751/250000000⟩
def contact0520 : RatBall := localContactBall tau0520 center0520
def work0520 : RoundedTauEval :=
  evalTau precision tau0520 contact0520 logTwoBall

theorem center_sq0520 : (center0520.re : ℝ)^2 +
    (center0520.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0520]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0520 : work0520.theta.ok = true ∧
    work0520.jac.invOK = true ∧ acceptsUnitSq work0520.out = true := by decide +kernel

def cell0520 : CellCertificate where
  tauBall := tau0520
  contactCenter := center0520
  contactBall := contact0520
  work := work0520
  center_sq := center_sq0520
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0520.1
  jac_ok := checks0520.2.1
  accepted := checks0520.2.2

def tau0521 : RatBall :=
  ⟨⟨-49/160, -21/160⟩, 3/320⟩
def center0521 : GaussianRat :=
  ⟨-41791301/200000000, -41587123/500000000⟩
def contact0521 : RatBall := localContactBall tau0521 center0521
def work0521 : RoundedTauEval :=
  evalTau precision tau0521 contact0521 logTwoBall

theorem center_sq0521 : (center0521.re : ℝ)^2 +
    (center0521.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0521]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0521 : work0521.theta.ok = true ∧
    work0521.jac.invOK = true ∧ acceptsUnitSq work0521.out = true := by decide +kernel

def cell0521 : CellCertificate where
  tauBall := tau0521
  contactCenter := center0521
  contactBall := contact0521
  work := work0521
  center_sq := center_sq0521
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0521.1
  jac_ok := checks0521.2.1
  accepted := checks0521.2.2

def tau0522 : RatBall :=
  ⟨⟨-11/32, -19/160⟩, 3/320⟩
def center0522 : GaussianRat :=
  ⟨-231972447/1000000000, -73469819/1000000000⟩
def contact0522 : RatBall := localContactBall tau0522 center0522
def work0522 : RoundedTauEval :=
  evalTau precision tau0522 contact0522 logTwoBall

theorem center_sq0522 : (center0522.re : ℝ)^2 +
    (center0522.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0522]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0522 : work0522.theta.ok = true ∧
    work0522.jac.invOK = true ∧ acceptsUnitSq work0522.out = true := by decide +kernel

def cell0522 : CellCertificate where
  tauBall := tau0522
  contactCenter := center0522
  contactBall := contact0522
  work := work0522
  center_sq := center_sq0522
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0522.1
  jac_ok := checks0522.2.1
  accepted := checks0522.2.2

def tau0523 : RatBall :=
  ⟨⟨-53/160, -19/160⟩, 3/320⟩
def center0523 : GaussianRat :=
  ⟨-56041997/250000000, -74061203/1000000000⟩
def contact0523 : RatBall := localContactBall tau0523 center0523
def work0523 : RoundedTauEval :=
  evalTau precision tau0523 contact0523 logTwoBall

theorem center_sq0523 : (center0523.re : ℝ)^2 +
    (center0523.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0523]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0523 : work0523.theta.ok = true ∧
    work0523.jac.invOK = true ∧ acceptsUnitSq work0523.out = true := by decide +kernel

def cell0523 : CellCertificate where
  tauBall := tau0523
  contactCenter := center0523
  contactBall := contact0523
  work := work0523
  center_sq := center_sq0523
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0523.1
  jac_ok := checks0523.2.1
  accepted := checks0523.2.2

def tau0524 : RatBall :=
  ⟨⟨-11/32, -17/160⟩, 3/320⟩
def center0524 : GaussianRat :=
  ⟨-57851871/250000000, -6570369/100000000⟩
def contact0524 : RatBall := localContactBall tau0524 center0524
def work0524 : RoundedTauEval :=
  evalTau precision tau0524 contact0524 logTwoBall

theorem center_sq0524 : (center0524.re : ℝ)^2 +
    (center0524.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0524]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0524 : work0524.theta.ok = true ∧
    work0524.jac.invOK = true ∧ acceptsUnitSq work0524.out = true := by decide +kernel

def cell0524 : CellCertificate where
  tauBall := tau0524
  contactCenter := center0524
  contactBall := contact0524
  work := work0524
  center_sq := center_sq0524
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0524.1
  jac_ok := checks0524.2.1
  accepted := checks0524.2.2

def tau0525 : RatBall :=
  ⟨⟨-53/160, -17/160⟩, 3/320⟩
def center0525 : GaussianRat :=
  ⟨-44722969/200000000, -66230667/1000000000⟩
def contact0525 : RatBall := localContactBall tau0525 center0525
def work0525 : RoundedTauEval :=
  evalTau precision tau0525 contact0525 logTwoBall

theorem center_sq0525 : (center0525.re : ℝ)^2 +
    (center0525.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0525]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0525 : work0525.theta.ok = true ∧
    work0525.jac.invOK = true ∧ acceptsUnitSq work0525.out = true := by decide +kernel

def cell0525 : CellCertificate where
  tauBall := tau0525
  contactCenter := center0525
  contactBall := contact0525
  work := work0525
  center_sq := center_sq0525
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0525.1
  jac_ok := checks0525.2.1
  accepted := checks0525.2.2

def tau0526 : RatBall :=
  ⟨⟨-47/160, -31/160⟩, 3/320⟩
def center0526 : GaussianRat :=
  ⟨-40948189/200000000, -124226081/1000000000⟩
def contact0526 : RatBall := localContactBall tau0526 center0526
def work0526 : RoundedTauEval :=
  evalTau precision tau0526 contact0526 logTwoBall

theorem center_sq0526 : (center0526.re : ℝ)^2 +
    (center0526.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0526]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0526 : work0526.theta.ok = true ∧
    work0526.jac.invOK = true ∧ acceptsUnitSq work0526.out = true := by decide +kernel

def cell0526 : CellCertificate where
  tauBall := tau0526
  contactCenter := center0526
  contactBall := contact0526
  work := work0526
  center_sq := center_sq0526
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0526.1
  jac_ok := checks0526.2.1
  accepted := checks0526.2.2

def tau0527 : RatBall :=
  ⟨⟨-9/32, -31/160⟩, 3/320⟩
def center0527 : GaussianRat :=
  ⟨-19656377/100000000, -125132383/1000000000⟩
def contact0527 : RatBall := localContactBall tau0527 center0527
def work0527 : RoundedTauEval :=
  evalTau precision tau0527 contact0527 logTwoBall

theorem center_sq0527 : (center0527.re : ℝ)^2 +
    (center0527.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0527]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0527 : work0527.theta.ok = true ∧
    work0527.jac.invOK = true ∧ acceptsUnitSq work0527.out = true := by decide +kernel

def cell0527 : CellCertificate where
  tauBall := tau0527
  contactCenter := center0527
  contactBall := contact0527
  work := work0527
  center_sq := center_sq0527
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0527.1
  jac_ok := checks0527.2.1
  accepted := checks0527.2.2

def cells : List CellCertificate := [cell0520, cell0521, cell0522, cell0523, cell0524, cell0525, cell0526, cell0527]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0065

end


