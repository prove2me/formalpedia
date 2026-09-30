-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0240_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0240_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:14:35.324687+00:00
-- url     : https://prove2.me/theorems/478f8c90-2f0b-455e-9ba5-f469186d4520
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0240 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0240_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1922 : (center1922.re : ℝ)^2 +
    (center1922.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1922]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1922 : work1922.theta.ok = true ∧
    work1922.jac.invOK = true ∧ acceptsUnitSq work1922.out = true := by decide +kernel

def cell1922 : CellCertificate where
  tauBall := tau1922
  contactCenter := center1922
  contactBall := contact1922
  work := work1922
  center_sq := center_sq1922
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1922.1
  jac_ok := checks1922.2.1
  accepted := checks1922.2.2

def tau1923 : RatBall :=
  ⟨⟨-19/64, 87/320⟩, 3/640⟩
def center1923 : GaussianRat :=
  ⟨-106965213/500000000, 35068781/200000000⟩
def contact1923 : RatBall := localContactBall tau1923 center1923
def work1923 : RoundedTauEval :=
  evalTau precision tau1923 contact1923 logTwoBall

theorem center_sq1923 : (center1923.re : ℝ)^2 +
    (center1923.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1923]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1923 : work1923.theta.ok = true ∧
    work1923.jac.invOK = true ∧ acceptsUnitSq work1923.out = true := by decide +kernel

def cell1923 : CellCertificate where
  tauBall := tau1923
  contactCenter := center1923
  contactBall := contact1923
  work := work1923
  center_sq := center_sq1923
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1923.1
  jac_ok := checks1923.2.1
  accepted := checks1923.2.2

def tau1924 : RatBall :=
  ⟨⟨-93/320, 87/320⟩, 3/640⟩
def center1924 : GaussianRat :=
  ⟨-1638777/7812500, 17602767/100000000⟩
def contact1924 : RatBall := localContactBall tau1924 center1924
def work1924 : RoundedTauEval :=
  evalTau precision tau1924 contact1924 logTwoBall

theorem center_sq1924 : (center1924.re : ℝ)^2 +
    (center1924.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1924]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1924 : work1924.theta.ok = true ∧
    work1924.jac.invOK = true ∧ acceptsUnitSq work1924.out = true := by decide +kernel

def cell1924 : CellCertificate where
  tauBall := tau1924
  contactCenter := center1924
  contactBall := contact1924
  work := work1924
  center_sq := center_sq1924
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1924.1
  jac_ok := checks1924.2.1
  accepted := checks1924.2.2

def tau1925 : RatBall :=
  ⟨⟨-91/320, 17/64⟩, 3/640⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240


