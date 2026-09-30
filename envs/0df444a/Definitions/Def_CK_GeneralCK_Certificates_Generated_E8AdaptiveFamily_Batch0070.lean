-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0070
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0070
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:25:57.404755+00:00
-- url     : https://prove2.me/theorems/90954184-4eb9-422b-a6a3-fa0ffa23fc0c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0070` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0070` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0070` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0070 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0070.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0070 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0070

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0560 : RatBall :=
  ⟨⟨3/160, -11/32⟩, 3/320⟩
def center0560 : GaussianRat :=
  ⟨7404737/500000000, -31086129/125000000⟩
def contact0560 : RatBall := localContactBall tau0560 center0560
def work0560 : RoundedTauEval :=
  evalTau precision tau0560 contact0560 logTwoBall

theorem center_sq0560 : (center0560.re : ℝ)^2 +
    (center0560.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0560]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0560 : work0560.theta.ok = true ∧
    work0560.jac.invOK = true ∧ acceptsUnitSq work0560.out = true := by decide +kernel

def cell0560 : CellCertificate where
  tauBall := tau0560
  contactCenter := center0560
  contactBall := contact0560
  work := work0560
  center_sq := center_sq0560
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0560.1
  jac_ok := checks0560.2.1
  accepted := checks0560.2.2

def tau0561 : RatBall :=
  ⟨⟨1/160, -53/160⟩, 3/320⟩
def center0561 : GaussianRat :=
  ⟨611093/125000000, -238963881/1000000000⟩
def contact0561 : RatBall := localContactBall tau0561 center0561
def work0561 : RoundedTauEval :=
  evalTau precision tau0561 contact0561 logTwoBall

theorem center_sq0561 : (center0561.re : ℝ)^2 +
    (center0561.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0561]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0561 : work0561.theta.ok = true ∧
    work0561.jac.invOK = true ∧ acceptsUnitSq work0561.out = true := by decide +kernel

def cell0561 : CellCertificate where
  tauBall := tau0561
  contactCenter := center0561
  contactBall := contact0561
  work := work0561
  center_sq := center_sq0561
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0561.1
  jac_ok := checks0561.2.1
  accepted := checks0561.2.2

def tau0562 : RatBall :=
  ⟨⟨3/160, -53/160⟩, 3/320⟩
def center0562 : GaussianRat :=
  ⟨1832943/125000000, -238869281/1000000000⟩
def contact0562 : RatBall := localContactBall tau0562 center0562
def work0562 : RoundedTauEval :=
  evalTau precision tau0562 contact0562 logTwoBall

theorem center_sq0562 : (center0562.re : ℝ)^2 +
    (center0562.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0562]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0562 : work0562.theta.ok = true ∧
    work0562.jac.invOK = true ∧ acceptsUnitSq work0562.out = true := by decide +kernel

def cell0562 : CellCertificate where
  tauBall := tau0562
  contactCenter := center0562
  contactBall := contact0562
  work := work0562
  center_sq := center_sq0562
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0562.1
  jac_ok := checks0562.2.1
  accepted := checks0562.2.2

def tau0563 : RatBall :=
  ⟨⟨1/32, -11/32⟩, 3/320⟩
def center0563 : GaussianRat :=
  ⟨24673061/1000000000, -248489097/1000000000⟩
def contact0563 : RatBall := localContactBall tau0563 center0563
def work0563 : RoundedTauEval :=
  evalTau precision tau0563 contact0563 logTwoBall

theorem center_sq0563 : (center0563.re : ℝ)^2 +
    (center0563.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0563]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0563 : work0563.theta.ok = true ∧
    work0563.jac.invOK = true ∧ acceptsUnitSq work0563.out = true := by decide +kernel

def cell0563 : CellCertificate where
  tauBall := tau0563
  contactCenter := center0563
  contactBall := contact0563
  work := work0563
  center_sq := center_sq0563
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0563.1
  jac_ok := checks0563.2.1
  accepted := checks0563.2.2

def tau0564 : RatBall :=
  ⟨⟨7/160, -11/32⟩, 3/320⟩
def center0564 : GaussianRat :=
  ⟨6904519/200000000, -248189889/1000000000⟩
def contact0564 : RatBall := localContactBall tau0564 center0564
def work0564 : RoundedTauEval :=
  evalTau precision tau0564 contact0564 logTwoBall

theorem center_sq0564 : (center0564.re : ℝ)^2 +
    (center0564.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0564]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0564 : work0564.theta.ok = true ∧
    work0564.jac.invOK = true ∧ acceptsUnitSq work0564.out = true := by decide +kernel

def cell0564 : CellCertificate where
  tauBall := tau0564
  contactCenter := center0564
  contactBall := contact0564
  work := work0564
  center_sq := center_sq0564
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0564.1
  jac_ok := checks0564.2.1
  accepted := checks0564.2.2

def tau0565 : RatBall :=
  ⟨⟨1/32, -53/160⟩, 3/320⟩
def center0565 : GaussianRat :=
  ⟨2443029/100000000, -119340169/500000000⟩
def contact0565 : RatBall := localContactBall tau0565 center0565
def work0565 : RoundedTauEval :=
  evalTau precision tau0565 contact0565 logTwoBall

theorem center_sq0565 : (center0565.re : ℝ)^2 +
    (center0565.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0565]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0565 : work0565.theta.ok = true ∧
    work0565.jac.invOK = true ∧ acceptsUnitSq work0565.out = true := by decide +kernel

def cell0565 : CellCertificate where
  tauBall := tau0565
  contactCenter := center0565
  contactBall := contact0565
  work := work0565
  center_sq := center_sq0565
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0565.1
  jac_ok := checks0565.2.1
  accepted := checks0565.2.2

def tau0566 : RatBall :=
  ⟨⟨7/160, -53/160⟩, 3/320⟩
def center0566 : GaussianRat :=
  ⟨17091823/500000000, -119198781/500000000⟩
def contact0566 : RatBall := localContactBall tau0566 center0566
def work0566 : RoundedTauEval :=
  evalTau precision tau0566 contact0566 logTwoBall

theorem center_sq0566 : (center0566.re : ℝ)^2 +
    (center0566.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0566]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0566 : work0566.theta.ok = true ∧
    work0566.jac.invOK = true ∧ acceptsUnitSq work0566.out = true := by decide +kernel

def cell0566 : CellCertificate where
  tauBall := tau0566
  contactCenter := center0566
  contactBall := contact0566
  work := work0566
  center_sq := center_sq0566
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0566.1
  jac_ok := checks0566.2.1
  accepted := checks0566.2.2

def tau0567 : RatBall :=
  ⟨⟨1/160, -51/160⟩, 3/320⟩
def center0567 : GaussianRat :=
  ⟨4842747/1000000000, -45846653/200000000⟩
def contact0567 : RatBall := localContactBall tau0567 center0567
def work0567 : RoundedTauEval :=
  evalTau precision tau0567 contact0567 logTwoBall

theorem center_sq0567 : (center0567.re : ℝ)^2 +
    (center0567.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0567]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0567 : work0567.theta.ok = true ∧
    work0567.jac.invOK = true ∧ acceptsUnitSq work0567.out = true := by decide +kernel

def cell0567 : CellCertificate where
  tauBall := tau0567
  contactCenter := center0567
  contactBall := contact0567
  work := work0567
  center_sq := center_sq0567
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0567.1
  jac_ok := checks0567.2.1
  accepted := checks0567.2.2

def cells : List CellCertificate := [cell0560, cell0561, cell0562, cell0563, cell0564, cell0565, cell0566, cell0567]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0070

end


