-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0240_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0240_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:01:34.669619+00:00
-- url     : https://prove2.me/theorems/2e81d53b-e931-4934-b1d5-06590431f9ab
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0240 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0240_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center1925 : GaussianRat :=
  ⟨-102458249/500000000, 172511057/1000000000⟩
def contact1925 : RatBall := localContactBall tau1925 center1925
def work1925 : RoundedTauEval :=
  evalTau precision tau1925 contact1925 logTwoBall

theorem center_sq1925 : (center1925.re : ℝ)^2 +
    (center1925.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1925]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1925 : work1925.theta.ok = true ∧
    work1925.jac.invOK = true ∧ acceptsUnitSq work1925.out = true := by decide +kernel

def cell1925 : CellCertificate where
  tauBall := tau1925
  contactCenter := center1925
  contactBall := contact1925
  work := work1925
  center_sq := center_sq1925
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1925.1
  jac_ok := checks1925.2.1
  accepted := checks1925.2.2

def tau1926 : RatBall :=
  ⟨⟨-89/320, 17/64⟩, 3/640⟩
def center1926 : GaussianRat :=
  ⟨-20072031/100000000, 86578791/500000000⟩
def contact1926 : RatBall := localContactBall tau1926 center1926
def work1926 : RoundedTauEval :=
  evalTau precision tau1926 contact1926 logTwoBall

theorem center_sq1926 : (center1926.re : ℝ)^2 +
    (center1926.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1926]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1926 : work1926.theta.ok = true ∧
    work1926.jac.invOK = true ∧ acceptsUnitSq work1926.out = true := by decide +kernel

def cell1926 : CellCertificate where
  tauBall := tau1926
  contactCenter := center1926
  contactBall := contact1926
  work := work1926
  center_sq := center_sq1926
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1926.1
  jac_ok := checks1926.2.1
  accepted := checks1926.2.2

def tau1927 : RatBall :=
  ⟨⟨-91/320, 87/320⟩, 3/640⟩
def center1927 : GaussianRat :=
  ⟨-102788551/500000000, 176702417/1000000000⟩
def contact1927 : RatBall := localContactBall tau1927 center1927
def work1927 : RoundedTauEval :=
  evalTau precision tau1927 contact1927 logTwoBall

theorem center_sq1927 : (center1927.re : ℝ)^2 +
    (center1927.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1927]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240


