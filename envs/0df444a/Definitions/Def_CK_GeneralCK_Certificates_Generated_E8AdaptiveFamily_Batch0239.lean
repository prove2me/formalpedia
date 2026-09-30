-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0239
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0239
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:55:23.605646+00:00
-- url     : https://prove2.me/theorems/cb3f1dee-b87a-48ae-8dde-91c201d6f8a4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0239.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0239_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1917 : RoundedTauEval :=
  evalTau precision tau1917 contact1917 logTwoBall

theorem center_sq1917 : (center1917.re : ℝ)^2 +
    (center1917.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1917]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1917 : work1917.theta.ok = true ∧
    work1917.jac.invOK = true ∧ acceptsUnitSq work1917.out = true := by decide +kernel

def cell1917 : CellCertificate where
  tauBall := tau1917
  contactCenter := center1917
  contactBall := contact1917
  work := work1917
  center_sq := center_sq1917
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1917.1
  jac_ok := checks1917.2.1
  accepted := checks1917.2.2

def tau1918 : RatBall :=
  ⟨⟨-89/320, 81/320⟩, 3/640⟩
def center1918 : GaussianRat :=
  ⟨-199473497/1000000000, 41191221/250000000⟩
def contact1918 : RatBall := localContactBall tau1918 center1918
def work1918 : RoundedTauEval :=
  evalTau precision tau1918 contact1918 logTwoBall

theorem center_sq1918 : (center1918.re : ℝ)^2 +
    (center1918.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1918]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1918 : work1918.theta.ok = true ∧
    work1918.jac.invOK = true ∧ acceptsUnitSq work1918.out = true := by decide +kernel

def cell1918 : CellCertificate where
  tauBall := tau1918
  contactCenter := center1918
  contactBall := contact1918
  work := work1918
  center_sq := center_sq1918
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1918.1
  jac_ok := checks1918.2.1
  accepted := checks1918.2.2

def tau1919 : RatBall :=
  ⟨⟨-91/320, 83/320⟩, 3/640⟩
def center1919 : GaussianRat :=
  ⟨-204274783/1000000000, 168328783/1000000000⟩
def contact1919 : RatBall := localContactBall tau1919 center1919
def work1919 : RoundedTauEval :=
  evalTau precision tau1919 contact1919 logTwoBall

theorem center_sq1919 : (center1919.re : ℝ)^2 +
    (center1919.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1919]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1919 : work1919.theta.ok = true ∧
    work1919.jac.invOK = true ∧ acceptsUnitSq work1919.out = true := by decide +kernel

def cell1919 : CellCertificate where
  tauBall := tau1919
  contactCenter := center1919
  contactBall := contact1919
  work := work1919
  center_sq := center_sq1919
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1919.1
  jac_ok := checks1919.2.1
  accepted := checks1919.2.2

def cells : List CellCertificate := [cell1912, cell1913, cell1914, cell1915, cell1916, cell1917, cell1918, cell1919]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239


