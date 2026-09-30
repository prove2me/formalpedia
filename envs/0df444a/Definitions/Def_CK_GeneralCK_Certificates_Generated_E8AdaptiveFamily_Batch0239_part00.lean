-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0239_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0239_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:11:57.534916+00:00
-- url     : https://prove2.me/theorems/7ca525d6-50b8-43f0-b1a4-a99a523dded8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0239 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1912 : RatBall :=
  ⟨⟨-93/320, 79/320⟩, 3/640⟩
def center1912 : GaussianRat :=
  ⟨-207198371/1000000000, 15939079/100000000⟩
def contact1912 : RatBall := localContactBall tau1912 center1912
def work1912 : RoundedTauEval :=
  evalTau precision tau1912 contact1912 logTwoBall

theorem center_sq1912 : (center1912.re : ℝ)^2 +
    (center1912.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1912]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1912 : work1912.theta.ok = true ∧
    work1912.jac.invOK = true ∧ acceptsUnitSq work1912.out = true := by decide +kernel

def cell1912 : CellCertificate where
  tauBall := tau1912
  contactCenter := center1912
  contactBall := contact1912
  work := work1912
  center_sq := center_sq1912
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1912.1
  jac_ok := checks1912.2.1
  accepted := checks1912.2.2

def tau1913 : RatBall :=
  ⟨⟨-19/64, 81/320⟩, 3/640⟩
def center1913 : GaussianRat :=
  ⟨-211952789/1000000000, 162910673/1000000000⟩
def contact1913 : RatBall := localContactBall tau1913 center1913
def work1913 : RoundedTauEval :=
  evalTau precision tau1913 contact1913 logTwoBall

theorem center_sq1913 : (center1913.re : ℝ)^2 +
    (center1913.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1913]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1913 : work1913.theta.ok = true ∧
    work1913.jac.invOK = true ∧ acceptsUnitSq work1913.out = true := by decide +kernel

def cell1913 : CellCertificate where
  tauBall := tau1913
  contactCenter := center1913
  contactBall := contact1913
  work := work1913
  center_sq := center_sq1913
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1913.1
  jac_ok := checks1913.2.1
  accepted := checks1913.2.2

def tau1914 : RatBall :=
  ⟨⟨-93/320, 81/320⟩, 3/640⟩
def center1914 : GaussianRat :=
  ⟨-103905761/500000000, 163537217/1000000000⟩
def contact1914 : RatBall := localContactBall tau1914 center1914
def work1914 : RoundedTauEval :=
  evalTau precision tau1914 contact1914 logTwoBall

theorem center_sq1914 : (center1914.re : ℝ)^2 +
    (center1914.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1914]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239


