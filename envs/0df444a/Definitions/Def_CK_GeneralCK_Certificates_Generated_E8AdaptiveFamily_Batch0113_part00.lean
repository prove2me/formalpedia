-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0113_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0113_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:40:29.205485+00:00
-- url     : https://prove2.me/theorems/e83a5d03-ea19-4488-95ea-7cbb57bcd63e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0113 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0904 : RatBall :=
  ⟨⟨-27/160, 39/160⟩, 3/320⟩
def center0904 : GaussianRat :=
  ⟨-123057717/1000000000, 167087407/1000000000⟩
def contact0904 : RatBall := localContactBall tau0904 center0904
def work0904 : RoundedTauEval :=
  evalTau precision tau0904 contact0904 logTwoBall

theorem center_sq0904 : (center0904.re : ℝ)^2 +
    (center0904.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0904]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0904 : work0904.theta.ok = true ∧
    work0904.jac.invOK = true ∧ acceptsUnitSq work0904.out = true := by decide +kernel

def cell0904 : CellCertificate where
  tauBall := tau0904
  contactCenter := center0904
  contactBall := contact0904
  work := work0904
  center_sq := center_sq0904
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0904.1
  jac_ok := checks0904.2.1
  accepted := checks0904.2.2

def tau0905 : RatBall :=
  ⟨⟨-5/32, 39/160⟩, 3/320⟩
def center0905 : GaussianRat :=
  ⟨-57074691/500000000, 83923163/500000000⟩
def contact0905 : RatBall := localContactBall tau0905 center0905
def work0905 : RoundedTauEval :=
  evalTau precision tau0905 contact0905 logTwoBall

theorem center_sq0905 : (center0905.re : ℝ)^2 +
    (center0905.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0905]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0905 : work0905.theta.ok = true ∧
    work0905.jac.invOK = true ∧ acceptsUnitSq work0905.out = true := by decide +kernel

def cell0905 : CellCertificate where
  tauBall := tau0905
  contactCenter := center0905
  contactBall := contact0905
  work := work0905
  center_sq := center_sq0905
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0905.1
  jac_ok := checks0905.2.1
  accepted := checks0905.2.2

def tau0906 : RatBall :=
  ⟨⟨-31/160, 41/160⟩, 3/320⟩
def center0906 : GaussianRat :=
  ⟨-8852011/62500000, 87111573/500000000⟩
def contact0906 : RatBall := localContactBall tau0906 center0906
def work0906 : RoundedTauEval :=
  evalTau precision tau0906 contact0906 logTwoBall

theorem center_sq0906 : (center0906.re : ℝ)^2 +
    (center0906.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0906]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0906 : work0906.theta.ok = true ∧
    work0906.jac.invOK = true ∧ acceptsUnitSq work0906.out = true := by decide +kernel

def cell0906 : CellCertificate where
  tauBall := tau0906
  contactCenter := center0906
  contactBall := contact0906
  work := work0906
  center_sq := center_sq0906
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0906.1
  jac_ok := checks0906.2.1
  accepted := checks0906.2.2

def tau0907 : RatBall :=
  ⟨⟨-29/160, 41/160⟩, 3/320⟩
def center0907 : GaussianRat :=
  ⟨-132776829/1000000000, 35027183/200000000⟩
def contact0907 : RatBall := localContactBall tau0907 center0907
def work0907 : RoundedTauEval :=
  evalTau precision tau0907 contact0907 logTwoBall

theorem center_sq0907 : (center0907.re : ℝ)^2 +
    (center0907.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0907]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0907 : work0907.theta.ok = true ∧
    work0907.jac.invOK = true ∧ acceptsUnitSq work0907.out = true := by decide +kernel

def cell0907 : CellCertificate where
  tauBall := tau0907
  contactCenter := center0907
  contactBall := contact0907
  work := work0907
  center_sq := center_sq0907
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0907.1
  jac_ok := checks0907.2.1
  accepted := checks0907.2.2

def tau0908 : RatBall :=
  ⟨⟨-31/160, 43/160⟩, 3/320⟩
def center0908 : GaussianRat :=
  ⟨-71299541/500000000, 91537843/500000000⟩
def contact0908 : RatBall := localContactBall tau0908 center0908
def work0908 : RoundedTauEval :=
  evalTau precision tau0908 contact0908 logTwoBall

theorem center_sq0908 : (center0908.re : ℝ)^2 +
    (center0908.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0908]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0908 : work0908.theta.ok = true ∧
    work0908.jac.invOK = true ∧ acceptsUnitSq work0908.out = true := by decide +kernel

def cell0908 : CellCertificate where
  tauBall := tau0908
  contactCenter := center0908
  contactBall := contact0908
  work := work0908
  center_sq := center_sq0908
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0908.1
  jac_ok := checks0908.2.1
  accepted := checks0908.2.2

def tau0909 : RatBall :=
  ⟨⟨-29/160, 43/160⟩, 3/320⟩
def center0909 : GaussianRat :=
  ⟨-66845797/500000000, 18404523/100000000⟩
def contact0909 : RatBall := localContactBall tau0909 center0909
def work0909 : RoundedTauEval :=
  evalTau precision tau0909 contact0909 logTwoBall

theorem center_sq0909 : (center0909.re : ℝ)^2 +
    (center0909.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0909]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0909 : work0909.theta.ok = true ∧
    work0909.jac.invOK = true ∧ acceptsUnitSq work0909.out = true := by decide +kernel

def cell0909 : CellCertificate where
  tauBall := tau0909
  contactCenter := center0909
  contactBall := contact0909
  work := work0909
  center_sq := center_sq0909
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0909.1
  jac_ok := checks0909.2.1
  accepted := checks0909.2.2

def tau0910 : RatBall :=
  ⟨⟨-27/160, 41/160⟩, 3/320⟩
def center0910 : GaussianRat :=
  ⟨-123867137/1000000000, 21999637/125000000⟩
def contact0910 : RatBall := localContactBall tau0910 center0910
def work0910 : RoundedTauEval :=
  evalTau precision tau0910 contact0910 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113


