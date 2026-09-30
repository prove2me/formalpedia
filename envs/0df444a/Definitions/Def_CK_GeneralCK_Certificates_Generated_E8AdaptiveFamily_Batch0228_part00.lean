-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0228_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0228_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:11:36.214991+00:00
-- url     : https://prove2.me/theorems/ff97eef2-154f-4a47-8cf2-6bfa006dc3a1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0228 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1824 : RatBall :=
  ⟨⟨89/320, -89/320⟩, 3/640⟩
def center1824 : GaussianRat :=
  ⟨40408359/200000000, -181587727/1000000000⟩
def contact1824 : RatBall := localContactBall tau1824 center1824
def work1824 : RoundedTauEval :=
  evalTau precision tau1824 contact1824 logTwoBall

theorem center_sq1824 : (center1824.re : ℝ)^2 +
    (center1824.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1824]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1824 : work1824.theta.ok = true ∧
    work1824.jac.invOK = true ∧ acceptsUnitSq work1824.out = true := by decide +kernel

def cell1824 : CellCertificate where
  tauBall := tau1824
  contactCenter := center1824
  contactBall := contact1824
  work := work1824
  center_sq := center_sq1824
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1824.1
  jac_ok := checks1824.2.1
  accepted := checks1824.2.2

def tau1825 : RatBall :=
  ⟨⟨91/320, -89/320⟩, 3/640⟩
def center1825 : GaussianRat :=
  ⟨103128439/500000000, -180903081/1000000000⟩
def contact1825 : RatBall := localContactBall tau1825 center1825
def work1825 : RoundedTauEval :=
  evalTau precision tau1825 contact1825 logTwoBall

theorem center_sq1825 : (center1825.re : ℝ)^2 +
    (center1825.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1825]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1825 : work1825.theta.ok = true ∧
    work1825.jac.invOK = true ∧ acceptsUnitSq work1825.out = true := by decide +kernel

def cell1825 : CellCertificate where
  tauBall := tau1825
  contactCenter := center1825
  contactBall := contact1825
  work := work1825
  center_sq := center_sq1825
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1825.1
  jac_ok := checks1825.2.1
  accepted := checks1825.2.2

def tau1826 : RatBall :=
  ⟨⟨93/320, -89/320⟩, 3/640⟩
def center1826 : GaussianRat :=
  ⟨84181/400000, -180208911/1000000000⟩
def contact1826 : RatBall := localContactBall tau1826 center1826
def work1826 : RoundedTauEval :=
  evalTau precision tau1826 contact1826 logTwoBall

theorem center_sq1826 : (center1826.re : ℝ)^2 +
    (center1826.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1826]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1826 : work1826.theta.ok = true ∧
    work1826.jac.invOK = true ∧ acceptsUnitSq work1826.out = true := by decide +kernel

def cell1826 : CellCertificate where
  tauBall := tau1826
  contactCenter := center1826
  contactBall := contact1826
  work := work1826
  center_sq := center_sq1826
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1826.1
  jac_ok := checks1826.2.1
  accepted := checks1826.2.2

def tau1827 : RatBall :=
  ⟨⟨81/320, -87/320⟩, 3/640⟩
def center1827 : GaussianRat :=
  ⟨9218121/50000000, -179930859/1000000000⟩
def contact1827 : RatBall := localContactBall tau1827 center1827
def work1827 : RoundedTauEval :=
  evalTau precision tau1827 contact1827 logTwoBall

theorem center_sq1827 : (center1827.re : ℝ)^2 +
    (center1827.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1827]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1827 : work1827.theta.ok = true ∧
    work1827.jac.invOK = true ∧ acceptsUnitSq work1827.out = true := by decide +kernel

def cell1827 : CellCertificate where
  tauBall := tau1827
  contactCenter := center1827
  contactBall := contact1827
  work := work1827
  center_sq := center_sq1827
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1827.1
  jac_ok := checks1827.2.1
  accepted := checks1827.2.2

def tau1828 : RatBall :=
  ⟨⟨83/320, -87/320⟩, 3/640⟩
def center1828 : GaussianRat :=
  ⟨188642281/1000000000, -22413187/125000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228


