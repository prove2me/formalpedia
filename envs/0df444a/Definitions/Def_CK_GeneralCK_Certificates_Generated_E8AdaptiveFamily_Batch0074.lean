-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0074
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0074
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:10:37.834829+00:00
-- url     : https://prove2.me/theorems/5c46d18f-a391-46a7-824f-3b743c10e7fa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0074` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0074` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0074` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0074 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0074.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0074 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0074

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0592 : RatBall :=
  ⟨⟨19/160, -49/160⟩, 3/320⟩
def center0592 : GaussianRat :=
  ⟨90499187/1000000000, -215867147/1000000000⟩
def contact0592 : RatBall := localContactBall tau0592 center0592
def work0592 : RoundedTauEval :=
  evalTau precision tau0592 contact0592 logTwoBall

theorem center_sq0592 : (center0592.re : ℝ)^2 +
    (center0592.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0592]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0592 : work0592.theta.ok = true ∧
    work0592.jac.invOK = true ∧ acceptsUnitSq work0592.out = true := by decide +kernel

def cell0592 : CellCertificate where
  tauBall := tau0592
  contactCenter := center0592
  contactBall := contact0592
  work := work0592
  center_sq := center_sq0592
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0592.1
  jac_ok := checks0592.2.1
  accepted := checks0592.2.2

def tau0593 : RatBall :=
  ⟨⟨21/160, -51/160⟩, 3/320⟩
def center0593 : GaussianRat :=
  ⟨100729897/1000000000, -44886561/200000000⟩
def contact0593 : RatBall := localContactBall tau0593 center0593
def work0593 : RoundedTauEval :=
  evalTau precision tau0593 contact0593 logTwoBall

theorem center_sq0593 : (center0593.re : ℝ)^2 +
    (center0593.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0593]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0593 : work0593.theta.ok = true ∧
    work0593.jac.invOK = true ∧ acceptsUnitSq work0593.out = true := by decide +kernel

def cell0593 : CellCertificate where
  tauBall := tau0593
  contactCenter := center0593
  contactBall := contact0593
  work := work0593
  center_sq := center_sq0593
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0593.1
  jac_ok := checks0593.2.1
  accepted := checks0593.2.2

def tau0594 : RatBall :=
  ⟨⟨21/160, -49/160⟩, 3/320⟩
def center0594 : GaussianRat :=
  ⟨9985979/100000000, -43011679/200000000⟩
def contact0594 : RatBall := localContactBall tau0594 center0594
def work0594 : RoundedTauEval :=
  evalTau precision tau0594 contact0594 logTwoBall

theorem center_sq0594 : (center0594.re : ℝ)^2 +
    (center0594.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0594]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0594 : work0594.theta.ok = true ∧
    work0594.jac.invOK = true ∧ acceptsUnitSq work0594.out = true := by decide +kernel

def cell0594 : CellCertificate where
  tauBall := tau0594
  contactCenter := center0594
  contactBall := contact0594
  work := work0594
  center_sq := center_sq0594
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0594.1
  jac_ok := checks0594.2.1
  accepted := checks0594.2.2

def tau0595 : RatBall :=
  ⟨⟨23/160, -49/160⟩, 3/320⟩
def center0595 : GaussianRat :=
  ⟨109172181/1000000000, -42835301/200000000⟩
def contact0595 : RatBall := localContactBall tau0595 center0595
def work0595 : RoundedTauEval :=
  evalTau precision tau0595 contact0595 logTwoBall

theorem center_sq0595 : (center0595.re : ℝ)^2 +
    (center0595.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0595]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0595 : work0595.theta.ok = true ∧
    work0595.jac.invOK = true ∧ acceptsUnitSq work0595.out = true := by decide +kernel

def cell0595 : CellCertificate where
  tauBall := tau0595
  contactCenter := center0595
  contactBall := contact0595
  work := work0595
  center_sq := center_sq0595
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0595.1
  jac_ok := checks0595.2.1
  accepted := checks0595.2.2

def tau0596 : RatBall :=
  ⟨⟨5/32, -49/160⟩, 3/320⟩
def center0596 : GaussianRat :=
  ⟨23686489/200000000, -53305887/250000000⟩
def contact0596 : RatBall := localContactBall tau0596 center0596
def work0596 : RoundedTauEval :=
  evalTau precision tau0596 contact0596 logTwoBall

theorem center_sq0596 : (center0596.re : ℝ)^2 +
    (center0596.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0596]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0596 : work0596.theta.ok = true ∧
    work0596.jac.invOK = true ∧ acceptsUnitSq work0596.out = true := by decide +kernel

def cell0596 : CellCertificate where
  tauBall := tau0596
  contactCenter := center0596
  contactBall := contact0596
  work := work0596
  center_sq := center_sq0596
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0596.1
  jac_ok := checks0596.2.1
  accepted := checks0596.2.2

def tau0597 : RatBall :=
  ⟨⟨27/160, -49/160⟩, 3/320⟩
def center0597 : GaussianRat :=
  ⟨3988651/31250000, -53050431/250000000⟩
def contact0597 : RatBall := localContactBall tau0597 center0597
def work0597 : RoundedTauEval :=
  evalTau precision tau0597 contact0597 logTwoBall

theorem center_sq0597 : (center0597.re : ℝ)^2 +
    (center0597.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0597]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0597 : work0597.theta.ok = true ∧
    work0597.jac.invOK = true ∧ acceptsUnitSq work0597.out = true := by decide +kernel

def cell0597 : CellCertificate where
  tauBall := tau0597
  contactCenter := center0597
  contactBall := contact0597
  work := work0597
  center_sq := center_sq0597
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0597.1
  jac_ok := checks0597.2.1
  accepted := checks0597.2.2

def tau0598 : RatBall :=
  ⟨⟨9/160, -47/160⟩, 3/320⟩
def center0598 : GaussianRat :=
  ⟨42754839/1000000000, -41848559/200000000⟩
def contact0598 : RatBall := localContactBall tau0598 center0598
def work0598 : RoundedTauEval :=
  evalTau precision tau0598 contact0598 logTwoBall

theorem center_sq0598 : (center0598.re : ℝ)^2 +
    (center0598.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0598]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0598 : work0598.theta.ok = true ∧
    work0598.jac.invOK = true ∧ acceptsUnitSq work0598.out = true := by decide +kernel

def cell0598 : CellCertificate where
  tauBall := tau0598
  contactCenter := center0598
  contactBall := contact0598
  work := work0598
  center_sq := center_sq0598
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0598.1
  jac_ok := checks0598.2.1
  accepted := checks0598.2.2

def tau0599 : RatBall :=
  ⟨⟨11/160, -47/160⟩, 3/320⟩
def center0599 : GaussianRat :=
  ⟨13053307/250000000, -208849073/1000000000⟩
def contact0599 : RatBall := localContactBall tau0599 center0599
def work0599 : RoundedTauEval :=
  evalTau precision tau0599 contact0599 logTwoBall

theorem center_sq0599 : (center0599.re : ℝ)^2 +
    (center0599.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0599]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0599 : work0599.theta.ok = true ∧
    work0599.jac.invOK = true ∧ acceptsUnitSq work0599.out = true := by decide +kernel

def cell0599 : CellCertificate where
  tauBall := tau0599
  contactCenter := center0599
  contactBall := contact0599
  work := work0599
  center_sq := center_sq0599
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0599.1
  jac_ok := checks0599.2.1
  accepted := checks0599.2.2

def cells : List CellCertificate := [cell0592, cell0593, cell0594, cell0595, cell0596, cell0597, cell0598, cell0599]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0074

end


