-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0235_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0235_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:20:53.839344+00:00
-- url     : https://prove2.me/theorems/2932557f-15f9-4e4c-ad36-ad42ec39e0dd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0235 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0235_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1882 : (center1882.re : ℝ)^2 +
    (center1882.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1882]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1882 : work1882.theta.ok = true ∧
    work1882.jac.invOK = true ∧ acceptsUnitSq work1882.out = true := by decide +kernel

def cell1882 : CellCertificate where
  tauBall := tau1882
  contactCenter := center1882
  contactBall := contact1882
  work := work1882
  center_sq := center_sq1882
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1882.1
  jac_ok := checks1882.2.1
  accepted := checks1882.2.2

def tau1883 : RatBall :=
  ⟨⟨-111/320, 13/64⟩, 3/640⟩
def center1883 : GaussianRat :=
  ⟨-239515009/1000000000, 31500643/250000000⟩
def contact1883 : RatBall := localContactBall tau1883 center1883
def work1883 : RoundedTauEval :=
  evalTau precision tau1883 contact1883 logTwoBall

theorem center_sq1883 : (center1883.re : ℝ)^2 +
    (center1883.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1883]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1883 : work1883.theta.ok = true ∧
    work1883.jac.invOK = true ∧ acceptsUnitSq work1883.out = true := by decide +kernel

def cell1883 : CellCertificate where
  tauBall := tau1883
  contactCenter := center1883
  contactBall := contact1883
  work := work1883
  center_sq := center_sq1883
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1883.1
  jac_ok := checks1883.2.1
  accepted := checks1883.2.2

def tau1884 : RatBall :=
  ⟨⟨-109/320, 13/64⟩, 3/640⟩
def center1884 : GaussianRat :=
  ⟨-29446781/125000000, 63266993/500000000⟩
def contact1884 : RatBall := localContactBall tau1884 center1884
def work1884 : RoundedTauEval :=
  evalTau precision tau1884 contact1884 logTwoBall

theorem center_sq1884 : (center1884.re : ℝ)^2 +
    (center1884.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1884]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1884 : work1884.theta.ok = true ∧
    work1884.jac.invOK = true ∧ acceptsUnitSq work1884.out = true := by decide +kernel

def cell1884 : CellCertificate where
  tauBall := tau1884
  contactCenter := center1884
  contactBall := contact1884
  work := work1884
  center_sq := center_sq1884
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1884.1
  jac_ok := checks1884.2.1
  accepted := checks1884.2.2

def tau1885 : RatBall :=
  ⟨⟨-109/320, 67/320⟩, 3/640⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235


