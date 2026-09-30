-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0235_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0235_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:08:08.238552+00:00
-- url     : https://prove2.me/theorems/85a4f059-5c79-43ed-8c6f-7fd2a370f41e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235 (part 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235 (part 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235 (part 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235 (part 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0235 (part 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1880 : RatBall :=
  ⟨⟨111/320, -13/64⟩, 3/640⟩
def center1880 : GaussianRat :=
  ⟨239515009/1000000000, -31500643/250000000⟩
def contact1880 : RatBall := localContactBall tau1880 center1880
def work1880 : RoundedTauEval :=
  evalTau precision tau1880 contact1880 logTwoBall

theorem center_sq1880 : (center1880.re : ℝ)^2 +
    (center1880.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1880]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1880 : work1880.theta.ok = true ∧
    work1880.jac.invOK = true ∧ acceptsUnitSq work1880.out = true := by decide +kernel

def cell1880 : CellCertificate where
  tauBall := tau1880
  contactCenter := center1880
  contactBall := contact1880
  work := work1880
  center_sq := center_sq1880
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1880.1
  jac_ok := checks1880.2.1
  accepted := checks1880.2.2

def tau1881 : RatBall :=
  ⟨⟨113/320, -61/320⟩, 3/640⟩
def center1881 : GaussianRat :=
  ⟨242396513/1000000000, -117649273/1000000000⟩
def contact1881 : RatBall := localContactBall tau1881 center1881
def work1881 : RoundedTauEval :=
  evalTau precision tau1881 contact1881 logTwoBall

theorem center_sq1881 : (center1881.re : ℝ)^2 +
    (center1881.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1881]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1881 : work1881.theta.ok = true ∧
    work1881.jac.invOK = true ∧ acceptsUnitSq work1881.out = true := by decide +kernel

def cell1881 : CellCertificate where
  tauBall := tau1881
  contactCenter := center1881
  contactBall := contact1881
  work := work1881
  center_sq := center_sq1881
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1881.1
  jac_ok := checks1881.2.1
  accepted := checks1881.2.2

def tau1882 : RatBall :=
  ⟨⟨-113/320, 61/320⟩, 3/640⟩
def center1882 : GaussianRat :=
  ⟨-242396513/1000000000, 117649273/1000000000⟩
def contact1882 : RatBall := localContactBall tau1882 center1882
def work1882 : RoundedTauEval :=
  evalTau precision tau1882 contact1882 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235


