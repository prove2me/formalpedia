-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0233_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0233_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:11:15.157969+00:00
-- url     : https://prove2.me/theorems/16cd6961-c394-4b2c-8e48-42caca4284bc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0233 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1864 : RatBall :=
  ⟨⟨101/320, -79/320⟩, 3/640⟩
def center1864 : GaussianRat :=
  ⟨111809453/500000000, -156912213/1000000000⟩
def contact1864 : RatBall := localContactBall tau1864 center1864
def work1864 : RoundedTauEval :=
  evalTau precision tau1864 contact1864 logTwoBall

theorem center_sq1864 : (center1864.re : ℝ)^2 +
    (center1864.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1864]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1864 : work1864.theta.ok = true ∧
    work1864.jac.invOK = true ∧ acceptsUnitSq work1864.out = true := by decide +kernel

def cell1864 : CellCertificate where
  tauBall := tau1864
  contactCenter := center1864
  contactBall := contact1864
  work := work1864
  center_sq := center_sq1864
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1864.1
  jac_ok := checks1864.2.1
  accepted := checks1864.2.2

def tau1865 : RatBall :=
  ⟨⟨101/320, -77/320⟩, 3/640⟩
def center1865 : GaussianRat :=
  ⟨111496867/500000000, -152848327/1000000000⟩
def contact1865 : RatBall := localContactBall tau1865 center1865
def work1865 : RoundedTauEval :=
  evalTau precision tau1865 contact1865 logTwoBall

theorem center_sq1865 : (center1865.re : ℝ)^2 +
    (center1865.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1865]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1865 : work1865.theta.ok = true ∧
    work1865.jac.invOK = true ∧ acceptsUnitSq work1865.out = true := by decide +kernel

def cell1865 : CellCertificate where
  tauBall := tau1865
  contactCenter := center1865
  contactBall := contact1865
  work := work1865
  center_sq := center_sq1865
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1865.1
  jac_ok := checks1865.2.1
  accepted := checks1865.2.2

def tau1866 : RatBall :=
  ⟨⟨103/320, -77/320⟩, 3/640⟩
def center1866 : GaussianRat :=
  ⟨113522317/500000000, -152229153/1000000000⟩
def contact1866 : RatBall := localContactBall tau1866 center1866
def work1866 : RoundedTauEval :=
  evalTau precision tau1866 contact1866 logTwoBall

theorem center_sq1866 : (center1866.re : ℝ)^2 +
    (center1866.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1866]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233


