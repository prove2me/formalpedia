-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0227_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0227_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:52:30.326388+00:00
-- url     : https://prove2.me/theorems/9bfbfd47-e678-45b7-ad99-a780082859b1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0227 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1816 : RatBall :=
  ⟨⟨83/320, -89/320⟩, 3/640⟩
def center1816 : GaussianRat :=
  ⟨189282071/1000000000, -183581561/1000000000⟩
def contact1816 : RatBall := localContactBall tau1816 center1816
def work1816 : RoundedTauEval :=
  evalTau precision tau1816 contact1816 logTwoBall

theorem center_sq1816 : (center1816.re : ℝ)^2 +
    (center1816.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1816]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1816 : work1816.theta.ok = true ∧
    work1816.jac.invOK = true ∧ acceptsUnitSq work1816.out = true := by decide +kernel

def cell1816 : CellCertificate where
  tauBall := tau1816
  contactCenter := center1816
  contactBall := contact1816
  work := work1816
  center_sq := center_sq1816
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1816.1
  jac_ok := checks1816.2.1
  accepted := checks1816.2.2

def tau1817 : RatBall :=
  ⟨⟨17/64, -91/320⟩, 3/640⟩
def center1817 : GaussianRat :=
  ⟨97111567/500000000, -37439051/200000000⟩
def contact1817 : RatBall := localContactBall tau1817 center1817
def work1817 : RoundedTauEval :=
  evalTau precision tau1817 contact1817 logTwoBall

theorem center_sq1817 : (center1817.re : ℝ)^2 +
    (center1817.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1817]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1817 : work1817.theta.ok = true ∧
    work1817.jac.invOK = true ∧ acceptsUnitSq work1817.out = true := by decide +kernel

def cell1817 : CellCertificate where
  tauBall := tau1817
  contactCenter := center1817
  contactBall := contact1817
  work := work1817
  center_sq := center_sq1817
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1817.1
  jac_ok := checks1817.2.1
  accepted := checks1817.2.2

def tau1818 : RatBall :=
  ⟨⟨87/320, -91/320⟩, 3/640⟩
def center1818 : GaussianRat :=
  ⟨49621711/250000000, -186511513/1000000000⟩
def contact1818 : RatBall := localContactBall tau1818 center1818
def work1818 : RoundedTauEval :=
  evalTau precision tau1818 contact1818 logTwoBall

theorem center_sq1818 : (center1818.re : ℝ)^2 +
    (center1818.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1818]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1818 : work1818.theta.ok = true ∧
    work1818.jac.invOK = true ∧ acceptsUnitSq work1818.out = true := by decide +kernel

def cell1818 : CellCertificate where
  tauBall := tau1818
  contactCenter := center1818
  contactBall := contact1818
  work := work1818
  center_sq := center_sq1818
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1818.1
  jac_ok := checks1818.2.1
  accepted := checks1818.2.2

def tau1819 : RatBall :=
  ⟨⟨17/64, -89/320⟩, 3/640⟩
def center1819 : GaussianRat :=
  ⟨24194269/125000000, -5716477/31250000⟩
def contact1819 : RatBall := localContactBall tau1819 center1819
def work1819 : RoundedTauEval :=
  evalTau precision tau1819 contact1819 logTwoBall

theorem center_sq1819 : (center1819.re : ℝ)^2 +
    (center1819.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1819]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1819 : work1819.theta.ok = true ∧
    work1819.jac.invOK = true ∧ acceptsUnitSq work1819.out = true := by decide +kernel

def cell1819 : CellCertificate where
  tauBall := tau1819
  contactCenter := center1819
  contactBall := contact1819
  work := work1819
  center_sq := center_sq1819
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1819.1
  jac_ok := checks1819.2.1
  accepted := checks1819.2.2

def tau1820 : RatBall :=
  ⟨⟨87/320, -89/320⟩, 3/640⟩
def center1820 : GaussianRat :=
  ⟨7912299/40000000, -91131277/500000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227


