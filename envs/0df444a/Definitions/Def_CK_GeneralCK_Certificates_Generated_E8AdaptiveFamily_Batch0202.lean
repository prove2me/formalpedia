-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0202
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0202
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:49:48.339548+00:00
-- url     : https://prove2.me/theorems/a494770d-7eb7-4693-a8db-8e7cbb3806b5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0202` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0202` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0202` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0202 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0202.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0202 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0202

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1616 : RatBall :=
  ⟨⟨31/320, -113/320⟩, 3/640⟩
def center1616 : GaussianRat :=
  ⟨15335517/200000000, -253142899/1000000000⟩
def contact1616 : RatBall := localContactBall tau1616 center1616
def work1616 : RoundedTauEval :=
  evalTau precision tau1616 contact1616 logTwoBall

theorem center_sq1616 : (center1616.re : ℝ)^2 +
    (center1616.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1616]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1616 : work1616.theta.ok = true ∧
    work1616.jac.invOK = true ∧ acceptsUnitSq work1616.out = true := by decide +kernel

def cell1616 : CellCertificate where
  tauBall := tau1616
  contactCenter := center1616
  contactBall := contact1616
  work := work1616
  center_sq := center_sq1616
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1616.1
  jac_ok := checks1616.2.1
  accepted := checks1616.2.2

def tau1617 : RatBall :=
  ⟨⟨21/320, -111/320⟩, 3/640⟩
def center1617 : GaussianRat :=
  ⟨51839561/1000000000, -31235321/125000000⟩
def contact1617 : RatBall := localContactBall tau1617 center1617
def work1617 : RoundedTauEval :=
  evalTau precision tau1617 contact1617 logTwoBall

theorem center_sq1617 : (center1617.re : ℝ)^2 +
    (center1617.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1617]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1617 : work1617.theta.ok = true ∧
    work1617.jac.invOK = true ∧ acceptsUnitSq work1617.out = true := by decide +kernel

def cell1617 : CellCertificate where
  tauBall := tau1617
  contactCenter := center1617
  contactBall := contact1617
  work := work1617
  center_sq := center_sq1617
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1617.1
  jac_ok := checks1617.2.1
  accepted := checks1617.2.2

def tau1618 : RatBall :=
  ⟨⟨23/320, -111/320⟩, 3/640⟩
def center1618 : GaussianRat :=
  ⟨11349381/200000000, -62401781/250000000⟩
def contact1618 : RatBall := localContactBall tau1618 center1618
def work1618 : RoundedTauEval :=
  evalTau precision tau1618 contact1618 logTwoBall

theorem center_sq1618 : (center1618.re : ℝ)^2 +
    (center1618.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1618]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1618 : work1618.theta.ok = true ∧
    work1618.jac.invOK = true ∧ acceptsUnitSq work1618.out = true := by decide +kernel

def cell1618 : CellCertificate where
  tauBall := tau1618
  contactCenter := center1618
  contactBall := contact1618
  work := work1618
  center_sq := center_sq1618
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1618.1
  jac_ok := checks1618.2.1
  accepted := checks1618.2.2

def tau1619 : RatBall :=
  ⟨⟨21/320, -109/320⟩, 3/640⟩
def center1619 : GaussianRat :=
  ⟨51579953/1000000000, -48996707/200000000⟩
def contact1619 : RatBall := localContactBall tau1619 center1619
def work1619 : RoundedTauEval :=
  evalTau precision tau1619 contact1619 logTwoBall

theorem center_sq1619 : (center1619.re : ℝ)^2 +
    (center1619.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1619]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1619 : work1619.theta.ok = true ∧
    work1619.jac.invOK = true ∧ acceptsUnitSq work1619.out = true := by decide +kernel

def cell1619 : CellCertificate where
  tauBall := tau1619
  contactCenter := center1619
  contactBall := contact1619
  work := work1619
  center_sq := center_sq1619
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1619.1
  jac_ok := checks1619.2.1
  accepted := checks1619.2.2

def tau1620 : RatBall :=
  ⟨⟨23/320, -109/320⟩, 3/640⟩
def center1620 : GaussianRat :=
  ⟨56463291/1000000000, -15294731/62500000⟩
def contact1620 : RatBall := localContactBall tau1620 center1620
def work1620 : RoundedTauEval :=
  evalTau precision tau1620 contact1620 logTwoBall

theorem center_sq1620 : (center1620.re : ℝ)^2 +
    (center1620.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1620]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1620 : work1620.theta.ok = true ∧
    work1620.jac.invOK = true ∧ acceptsUnitSq work1620.out = true := by decide +kernel

def cell1620 : CellCertificate where
  tauBall := tau1620
  contactCenter := center1620
  contactBall := contact1620
  work := work1620
  center_sq := center_sq1620
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1620.1
  jac_ok := checks1620.2.1
  accepted := checks1620.2.2

def tau1621 : RatBall :=
  ⟨⟨5/64, -111/320⟩, 3/640⟩
def center1621 : GaussianRat :=
  ⟨30823109/500000000, -249307439/1000000000⟩
def contact1621 : RatBall := localContactBall tau1621 center1621
def work1621 : RoundedTauEval :=
  evalTau precision tau1621 contact1621 logTwoBall

theorem center_sq1621 : (center1621.re : ℝ)^2 +
    (center1621.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1621]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1621 : work1621.theta.ok = true ∧
    work1621.jac.invOK = true ∧ acceptsUnitSq work1621.out = true := by decide +kernel

def cell1621 : CellCertificate where
  tauBall := tau1621
  contactCenter := center1621
  contactBall := contact1621
  work := work1621
  center_sq := center_sq1621
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1621.1
  jac_ok := checks1621.2.1
  accepted := checks1621.2.2

def tau1622 : RatBall :=
  ⟨⟨27/320, -111/320⟩, 3/640⟩
def center1622 : GaussianRat :=
  ⟨66536837/1000000000, -62245929/250000000⟩
def contact1622 : RatBall := localContactBall tau1622 center1622
def work1622 : RoundedTauEval :=
  evalTau precision tau1622 contact1622 logTwoBall

theorem center_sq1622 : (center1622.re : ℝ)^2 +
    (center1622.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1622]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1622 : work1622.theta.ok = true ∧
    work1622.jac.invOK = true ∧ acceptsUnitSq work1622.out = true := by decide +kernel

def cell1622 : CellCertificate where
  tauBall := tau1622
  contactCenter := center1622
  contactBall := contact1622
  work := work1622
  center_sq := center_sq1622
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1622.1
  jac_ok := checks1622.2.1
  accepted := checks1622.2.2

def tau1623 : RatBall :=
  ⟨⟨5/64, -109/320⟩, 3/640⟩
def center1623 : GaussianRat :=
  ⟨6133879/100000000, -244424273/1000000000⟩
def contact1623 : RatBall := localContactBall tau1623 center1623
def work1623 : RoundedTauEval :=
  evalTau precision tau1623 contact1623 logTwoBall

theorem center_sq1623 : (center1623.re : ℝ)^2 +
    (center1623.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1623]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1623 : work1623.theta.ok = true ∧
    work1623.jac.invOK = true ∧ acceptsUnitSq work1623.out = true := by decide +kernel

def cell1623 : CellCertificate where
  tauBall := tau1623
  contactCenter := center1623
  contactBall := contact1623
  work := work1623
  center_sq := center_sq1623
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1623.1
  jac_ok := checks1623.2.1
  accepted := checks1623.2.2

def cells : List CellCertificate := [cell1616, cell1617, cell1618, cell1619, cell1620, cell1621, cell1622, cell1623]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0202

end


