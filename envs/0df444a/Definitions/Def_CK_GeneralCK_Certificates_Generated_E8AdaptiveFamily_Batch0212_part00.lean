-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0212_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0212_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:31:34.740078+00:00
-- url     : https://prove2.me/theorems/5875d845-807e-41b2-9549-8892a569f918
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0212 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1696 : RatBall :=
  ⟨⟨11/64, -107/320⟩, 3/640⟩
def center1696 : GaussianRat :=
  ⟨66249189/500000000, -232719989/1000000000⟩
def contact1696 : RatBall := localContactBall tau1696 center1696
def work1696 : RoundedTauEval :=
  evalTau precision tau1696 contact1696 logTwoBall

theorem center_sq1696 : (center1696.re : ℝ)^2 +
    (center1696.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1696]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1696 : work1696.theta.ok = true ∧
    work1696.jac.invOK = true ∧ acceptsUnitSq work1696.out = true := by decide +kernel

def cell1696 : CellCertificate where
  tauBall := tau1696
  contactCenter := center1696
  contactBall := contact1696
  work := work1696
  center_sq := center_sq1696
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1696.1
  jac_ok := checks1696.2.1
  accepted := checks1696.2.2

def tau1697 : RatBall :=
  ⟨⟨53/320, -21/64⟩, 3/640⟩
def center1697 : GaussianRat :=
  ⟨127250921/1000000000, -228652029/1000000000⟩
def contact1697 : RatBall := localContactBall tau1697 center1697
def work1697 : RoundedTauEval :=
  evalTau precision tau1697 contact1697 logTwoBall

theorem center_sq1697 : (center1697.re : ℝ)^2 +
    (center1697.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1697]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1697 : work1697.theta.ok = true ∧
    work1697.jac.invOK = true ∧ acceptsUnitSq work1697.out = true := by decide +kernel

def cell1697 : CellCertificate where
  tauBall := tau1697
  contactCenter := center1697
  contactBall := contact1697
  work := work1697
  center_sq := center_sq1697
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1697.1
  jac_ok := checks1697.2.1
  accepted := checks1697.2.2

def tau1698 : RatBall :=
  ⟨⟨11/64, -21/64⟩, 3/640⟩
def center1698 : GaussianRat :=
  ⟨65949739/500000000, -57017591/250000000⟩
def contact1698 : RatBall := localContactBall tau1698 center1698
def work1698 : RoundedTauEval :=
  evalTau precision tau1698 contact1698 logTwoBall

theorem center_sq1698 : (center1698.re : ℝ)^2 +
    (center1698.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1698]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1698 : work1698.theta.ok = true ∧
    work1698.jac.invOK = true ∧ acceptsUnitSq work1698.out = true := by decide +kernel

def cell1698 : CellCertificate where
  tauBall := tau1698
  contactCenter := center1698
  contactBall := contact1698
  work := work1698
  center_sq := center_sq1698
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1698.1
  jac_ok := checks1698.2.1
  accepted := checks1698.2.2

def tau1699 : RatBall :=
  ⟨⟨57/320, -111/320⟩, 3/640⟩
def center1699 : GaussianRat :=
  ⟨138434183/1000000000, -120712289/500000000⟩
def contact1699 : RatBall := localContactBall tau1699 center1699
def work1699 : RoundedTauEval :=
  evalTau precision tau1699 contact1699 logTwoBall

theorem center_sq1699 : (center1699.re : ℝ)^2 +
    (center1699.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1699]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1699 : work1699.theta.ok = true ∧
    work1699.jac.invOK = true ∧ acceptsUnitSq work1699.out = true := by decide +kernel

def cell1699 : CellCertificate where
  tauBall := tau1699
  contactCenter := center1699
  contactBall := contact1699
  work := work1699
  center_sq := center_sq1699
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1699.1
  jac_ok := checks1699.2.1
  accepted := checks1699.2.2

def tau1700 : RatBall :=
  ⟨⟨59/320, -111/320⟩, 3/640⟩
def center1700 : GaussianRat :=
  ⟨143104409/1000000000, -240754941/1000000000⟩
def contact1700 : RatBall := localContactBall tau1700 center1700

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212


