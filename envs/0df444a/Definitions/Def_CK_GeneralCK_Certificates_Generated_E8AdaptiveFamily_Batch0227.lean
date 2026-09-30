-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0227
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0227
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:36:36.925887+00:00
-- url     : https://prove2.me/theorems/863c978e-4f50-47f4-aa05-02b302de8730
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0227.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0227_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact1820 : RatBall := localContactBall tau1820 center1820
def work1820 : RoundedTauEval :=
  evalTau precision tau1820 contact1820 logTwoBall

theorem center_sq1820 : (center1820.re : ℝ)^2 +
    (center1820.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1820]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1820 : work1820.theta.ok = true ∧
    work1820.jac.invOK = true ∧ acceptsUnitSq work1820.out = true := by decide +kernel

def cell1820 : CellCertificate where
  tauBall := tau1820
  contactCenter := center1820
  contactBall := contact1820
  work := work1820
  center_sq := center_sq1820
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1820.1
  jac_ok := checks1820.2.1
  accepted := checks1820.2.2

def tau1821 : RatBall :=
  ⟨⟨89/320, -93/320⟩, 3/640⟩
def center1821 : GaussianRat :=
  ⟨50860061/250000000, -2969643/15625000⟩
def contact1821 : RatBall := localContactBall tau1821 center1821
def work1821 : RoundedTauEval :=
  evalTau precision tau1821 contact1821 logTwoBall

theorem center_sq1821 : (center1821.re : ℝ)^2 +
    (center1821.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1821]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1821 : work1821.theta.ok = true ∧
    work1821.jac.invOK = true ∧ acceptsUnitSq work1821.out = true := by decide +kernel

def cell1821 : CellCertificate where
  tauBall := tau1821
  contactCenter := center1821
  contactBall := contact1821
  work := work1821
  center_sq := center_sq1821
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1821.1
  jac_ok := checks1821.2.1
  accepted := checks1821.2.2

def tau1822 : RatBall :=
  ⟨⟨89/320, -91/320⟩, 3/640⟩
def center1822 : GaussianRat :=
  ⟨202731249/1000000000, -37163483/200000000⟩
def contact1822 : RatBall := localContactBall tau1822 center1822
def work1822 : RoundedTauEval :=
  evalTau precision tau1822 contact1822 logTwoBall

theorem center_sq1822 : (center1822.re : ℝ)^2 +
    (center1822.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1822]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1822 : work1822.theta.ok = true ∧
    work1822.jac.invOK = true ∧ acceptsUnitSq work1822.out = true := by decide +kernel

def cell1822 : CellCertificate where
  tauBall := tau1822
  contactCenter := center1822
  contactBall := contact1822
  work := work1822
  center_sq := center_sq1822
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1822.1
  jac_ok := checks1822.2.1
  accepted := checks1822.2.2

def tau1823 : RatBall :=
  ⟨⟨91/320, -91/320⟩, 3/640⟩
def center1823 : GaussianRat :=
  ⟨51739029/250000000, -46278317/250000000⟩
def contact1823 : RatBall := localContactBall tau1823 center1823
def work1823 : RoundedTauEval :=
  evalTau precision tau1823 contact1823 logTwoBall

theorem center_sq1823 : (center1823.re : ℝ)^2 +
    (center1823.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1823]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1823 : work1823.theta.ok = true ∧
    work1823.jac.invOK = true ∧ acceptsUnitSq work1823.out = true := by decide +kernel

def cell1823 : CellCertificate where
  tauBall := tau1823
  contactCenter := center1823
  contactBall := contact1823
  work := work1823
  center_sq := center_sq1823
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1823.1
  jac_ok := checks1823.2.1
  accepted := checks1823.2.2

def cells : List CellCertificate := [cell1816, cell1817, cell1818, cell1819, cell1820, cell1821, cell1822, cell1823]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227


