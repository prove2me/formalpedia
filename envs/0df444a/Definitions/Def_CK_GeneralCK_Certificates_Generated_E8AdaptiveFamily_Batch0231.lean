-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0231
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0231
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:04:07.42535+00:00
-- url     : https://prove2.me/theorems/7260bb86-71e6-4286-83c0-4e7a0e80dd1a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0231.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0231_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1852 : RoundedTauEval :=
  evalTau precision tau1852 contact1852 logTwoBall

theorem center_sq1852 : (center1852.re : ℝ)^2 +
    (center1852.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1852]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1852 : work1852.theta.ok = true ∧
    work1852.jac.invOK = true ∧ acceptsUnitSq work1852.out = true := by decide +kernel

def cell1852 : CellCertificate where
  tauBall := tau1852
  contactCenter := center1852
  contactBall := contact1852
  work := work1852
  center_sq := center_sq1852
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1852.1
  jac_ok := checks1852.2.1
  accepted := checks1852.2.2

def tau1853 : RatBall :=
  ⟨⟨93/320, -77/320⟩, 3/640⟩
def center1853 : GaussianRat :=
  ⟨12912721/62500000, -7762627/50000000⟩
def contact1853 : RatBall := localContactBall tau1853 center1853
def work1853 : RoundedTauEval :=
  evalTau precision tau1853 contact1853 logTwoBall

theorem center_sq1853 : (center1853.re : ℝ)^2 +
    (center1853.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1853]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1853 : work1853.theta.ok = true ∧
    work1853.jac.invOK = true ∧ acceptsUnitSq work1853.out = true := by decide +kernel

def cell1853 : CellCertificate where
  tauBall := tau1853
  contactCenter := center1853
  contactBall := contact1853
  work := work1853
  center_sq := center_sq1853
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1853.1
  jac_ok := checks1853.2.1
  accepted := checks1853.2.2

def tau1854 : RatBall :=
  ⟨⟨19/64, -77/320⟩, 3/640⟩
def center1854 : GaussianRat :=
  ⟨26341087/125000000, -77331419/500000000⟩
def contact1854 : RatBall := localContactBall tau1854 center1854
def work1854 : RoundedTauEval :=
  evalTau precision tau1854 contact1854 logTwoBall

theorem center_sq1854 : (center1854.re : ℝ)^2 +
    (center1854.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1854]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1854 : work1854.theta.ok = true ∧
    work1854.jac.invOK = true ∧ acceptsUnitSq work1854.out = true := by decide +kernel

def cell1854 : CellCertificate where
  tauBall := tau1854
  contactCenter := center1854
  contactBall := contact1854
  work := work1854
  center_sq := center_sq1854
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1854.1
  jac_ok := checks1854.2.1
  accepted := checks1854.2.2

def tau1855 : RatBall :=
  ⟨⟨97/320, -17/64⟩, 3/640⟩
def center1855 : GaussianRat :=
  ⟨54347721/250000000, -170518079/1000000000⟩
def contact1855 : RatBall := localContactBall tau1855 center1855
def work1855 : RoundedTauEval :=
  evalTau precision tau1855 contact1855 logTwoBall

theorem center_sq1855 : (center1855.re : ℝ)^2 +
    (center1855.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1855]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1855 : work1855.theta.ok = true ∧
    work1855.jac.invOK = true ∧ acceptsUnitSq work1855.out = true := by decide +kernel

def cell1855 : CellCertificate where
  tauBall := tau1855
  contactCenter := center1855
  contactBall := contact1855
  work := work1855
  center_sq := center_sq1855
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1855.1
  jac_ok := checks1855.2.1
  accepted := checks1855.2.2

def cells : List CellCertificate := [cell1848, cell1849, cell1850, cell1851, cell1852, cell1853, cell1854, cell1855]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231


