-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0228
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0228
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:29:13.918689+00:00
-- url     : https://prove2.me/theorems/41c68c48-c215-41cc-8cd4-bbaf8c87b398
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0228.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0228_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact1828 : RatBall := localContactBall tau1828 center1828
def work1828 : RoundedTauEval :=
  evalTau precision tau1828 contact1828 logTwoBall

theorem center_sq1828 : (center1828.re : ℝ)^2 +
    (center1828.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1828]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1828 : work1828.theta.ok = true ∧
    work1828.jac.invOK = true ∧ acceptsUnitSq work1828.out = true := by decide +kernel

def cell1828 : CellCertificate where
  tauBall := tau1828
  contactCenter := center1828
  contactBall := contact1828
  work := work1828
  center_sq := center_sq1828
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1828.1
  jac_ok := checks1828.2.1
  accepted := checks1828.2.2

def tau1829 : RatBall :=
  ⟨⟨81/320, -17/64⟩, 3/640⟩
def center1829 : GaussianRat :=
  ⟨36750261/200000000, -1756473/10000000⟩
def contact1829 : RatBall := localContactBall tau1829 center1829
def work1829 : RoundedTauEval :=
  evalTau precision tau1829 contact1829 logTwoBall

theorem center_sq1829 : (center1829.re : ℝ)^2 +
    (center1829.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1829]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1829 : work1829.theta.ok = true ∧
    work1829.jac.invOK = true ∧ acceptsUnitSq work1829.out = true := by decide +kernel

def cell1829 : CellCertificate where
  tauBall := tau1829
  contactCenter := center1829
  contactBall := contact1829
  work := work1829
  center_sq := center_sq1829
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1829.1
  jac_ok := checks1829.2.1
  accepted := checks1829.2.2

def tau1830 : RatBall :=
  ⟨⟨83/320, -17/64⟩, 3/640⟩
def center1830 : GaussianRat :=
  ⟨188020707/1000000000, -4375997/25000000⟩
def contact1830 : RatBall := localContactBall tau1830 center1830
def work1830 : RoundedTauEval :=
  evalTau precision tau1830 contact1830 logTwoBall

theorem center_sq1830 : (center1830.re : ℝ)^2 +
    (center1830.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1830]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1830 : work1830.theta.ok = true ∧
    work1830.jac.invOK = true ∧ acceptsUnitSq work1830.out = true := by decide +kernel

def cell1830 : CellCertificate where
  tauBall := tau1830
  contactCenter := center1830
  contactBall := contact1830
  work := work1830
  center_sq := center_sq1830
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1830.1
  jac_ok := checks1830.2.1
  accepted := checks1830.2.2

def tau1831 : RatBall :=
  ⟨⟨17/64, -87/320⟩, 3/640⟩
def center1831 : GaussianRat :=
  ⟨192903929/1000000000, -35733937/200000000⟩
def contact1831 : RatBall := localContactBall tau1831 center1831
def work1831 : RoundedTauEval :=
  evalTau precision tau1831 contact1831 logTwoBall

theorem center_sq1831 : (center1831.re : ℝ)^2 +
    (center1831.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1831]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1831 : work1831.theta.ok = true ∧
    work1831.jac.invOK = true ∧ acceptsUnitSq work1831.out = true := by decide +kernel

def cell1831 : CellCertificate where
  tauBall := tau1831
  contactCenter := center1831
  contactBall := contact1831
  work := work1831
  center_sq := center_sq1831
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1831.1
  jac_ok := checks1831.2.1
  accepted := checks1831.2.2

def cells : List CellCertificate := [cell1824, cell1825, cell1826, cell1827, cell1828, cell1829, cell1830, cell1831]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228


