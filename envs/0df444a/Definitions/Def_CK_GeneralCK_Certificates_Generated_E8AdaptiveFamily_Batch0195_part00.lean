-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0195_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0195_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:18:39.355305+00:00
-- url     : https://prove2.me/theorems/bc5fd6b9-ba12-4171-be78-df2a69a5acab
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0195 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1560 : RatBall :=
  ⟨⟨1/64, -117/320⟩, 3/640⟩
def center1560 : GaussianRat :=
  ⟨1257211/100000000, -66538831/250000000⟩
def contact1560 : RatBall := localContactBall tau1560 center1560
def work1560 : RoundedTauEval :=
  evalTau precision tau1560 contact1560 logTwoBall

theorem center_sq1560 : (center1560.re : ℝ)^2 +
    (center1560.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1560]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1560 : work1560.theta.ok = true ∧
    work1560.jac.invOK = true ∧ acceptsUnitSq work1560.out = true := by decide +kernel

def cell1560 : CellCertificate where
  tauBall := tau1560
  contactCenter := center1560
  contactBall := contact1560
  work := work1560
  center_sq := center_sq1560
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1560.1
  jac_ok := checks1560.2.1
  accepted := checks1560.2.2

def tau1561 : RatBall :=
  ⟨⟨7/320, -117/320⟩, 3/640⟩
def center1561 : GaussianRat :=
  ⟨3519651/200000000, -8314767/31250000⟩
def contact1561 : RatBall := localContactBall tau1561 center1561
def work1561 : RoundedTauEval :=
  evalTau precision tau1561 contact1561 logTwoBall

theorem center_sq1561 : (center1561.re : ℝ)^2 +
    (center1561.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1561]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1561 : work1561.theta.ok = true ∧
    work1561.jac.invOK = true ∧ acceptsUnitSq work1561.out = true := by decide +kernel

def cell1561 : CellCertificate where
  tauBall := tau1561
  contactCenter := center1561
  contactBall := contact1561
  work := work1561
  center_sq := center_sq1561
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1561.1
  jac_ok := checks1561.2.1
  accepted := checks1561.2.2

def tau1562 : RatBall :=
  ⟨⟨1/64, -23/64⟩, 3/640⟩
def center1562 : GaussianRat :=
  ⟨1563007/125000000, -13057087/50000000⟩
def contact1562 : RatBall := localContactBall tau1562 center1562
def work1562 : RoundedTauEval :=
  evalTau precision tau1562 contact1562 logTwoBall

theorem center_sq1562 : (center1562.re : ℝ)^2 +
    (center1562.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1562]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1562 : work1562.theta.ok = true ∧
    work1562.jac.invOK = true ∧ acceptsUnitSq work1562.out = true := by decide +kernel

def cell1562 : CellCertificate where
  tauBall := tau1562
  contactCenter := center1562
  contactBall := contact1562
  work := work1562
  center_sq := center_sq1562
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1562.1
  jac_ok := checks1562.2.1
  accepted := checks1562.2.2

def tau1563 : RatBall :=
  ⟨⟨7/320, -23/64⟩, 3/640⟩
def center1563 : GaussianRat :=
  ⟨350061/20000000, -130530621/500000000⟩
def contact1563 : RatBall := localContactBall tau1563 center1563
def work1563 : RoundedTauEval :=
  evalTau precision tau1563 contact1563 logTwoBall

theorem center_sq1563 : (center1563.re : ℝ)^2 +
    (center1563.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1563]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1563 : work1563.theta.ok = true ∧
    work1563.jac.invOK = true ∧ acceptsUnitSq work1563.out = true := by decide +kernel

def cell1563 : CellCertificate where
  tauBall := tau1563
  contactCenter := center1563
  contactBall := contact1563
  work := work1563
  center_sq := center_sq1563
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1563.1
  jac_ok := checks1563.2.1
  accepted := checks1563.2.2

def tau1564 : RatBall :=
  ⟨⟨1/64, -113/320⟩, 3/640⟩
def center1564 : GaussianRat :=
  ⟨12437881/1000000000, -3201937/12500000⟩
def contact1564 : RatBall := localContactBall tau1564 center1564
def work1564 : RoundedTauEval :=
  evalTau precision tau1564 contact1564 logTwoBall

theorem center_sq1564 : (center1564.re : ℝ)^2 +
    (center1564.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1564]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1564 : work1564.theta.ok = true ∧
    work1564.jac.invOK = true ∧ acceptsUnitSq work1564.out = true := by decide +kernel

def cell1564 : CellCertificate where
  tauBall := tau1564
  contactCenter := center1564
  contactBall := contact1564
  work := work1564
  center_sq := center_sq1564
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1564.1
  jac_ok := checks1564.2.1
  accepted := checks1564.2.2

def tau1565 : RatBall :=
  ⟨⟨7/320, -113/320⟩, 3/640⟩
def center1565 : GaussianRat :=
  ⟨17410471/1000000000, -51215337/200000000⟩
def contact1565 : RatBall := localContactBall tau1565 center1565
def work1565 : RoundedTauEval :=
  evalTau precision tau1565 contact1565 logTwoBall

theorem center_sq1565 : (center1565.re : ℝ)^2 +
    (center1565.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1565]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1565 : work1565.theta.ok = true ∧
    work1565.jac.invOK = true ∧ acceptsUnitSq work1565.out = true := by decide +kernel

def cell1565 : CellCertificate where
  tauBall := tau1565
  contactCenter := center1565
  contactBall := contact1565
  work := work1565
  center_sq := center_sq1565
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1565.1
  jac_ok := checks1565.2.1
  accepted := checks1565.2.2

def tau1566 : RatBall :=
  ⟨⟨9/320, -119/320⟩, 3/640⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195


