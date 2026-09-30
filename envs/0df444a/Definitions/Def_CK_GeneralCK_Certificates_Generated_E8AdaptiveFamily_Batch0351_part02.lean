-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0351_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0351_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:10:14.588419+00:00
-- url     : https://prove2.me/theorems/c5685b53-ebe5-44fc-ae01-17b56f2787d7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0351 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0351_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact2812 : RatBall := localContactBall tau2812 center2812
def work2812 : RoundedTauEval :=
  evalTau precision tau2812 contact2812 logTwoBall

theorem center_sq2812 : (center2812.re : ℝ)^2 +
    (center2812.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2812]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2812 : work2812.theta.ok = true ∧
    work2812.jac.invOK = true ∧ acceptsUnitSq work2812.out = true := by decide +kernel

def cell2812 : CellCertificate where
  tauBall := tau2812
  contactCenter := center2812
  contactBall := contact2812
  work := work2812
  center_sq := center_sq2812
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2812.1
  jac_ok := checks2812.2.1
  accepted := checks2812.2.2

def tau2813 : RatBall :=
  ⟨⟨-5/128, -51/128⟩, 3/1280⟩
def center2813 : GaussianRat :=
  ⟨-32375263/1000000000, -292424289/1000000000⟩
def contact2813 : RatBall := localContactBall tau2813 center2813
def work2813 : RoundedTauEval :=
  evalTau precision tau2813 contact2813 logTwoBall

theorem center_sq2813 : (center2813.re : ℝ)^2 +
    (center2813.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2813]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2813 : work2813.theta.ok = true ∧
    work2813.jac.invOK = true ∧ acceptsUnitSq work2813.out = true := by decide +kernel

def cell2813 : CellCertificate where
  tauBall := tau2813
  contactCenter := center2813
  contactBall := contact2813
  work := work2813
  center_sq := center_sq2813
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2813.1
  jac_ok := checks2813.2.1
  accepted := checks2813.2.2

def tau2814 : RatBall :=
  ⟨⟨-27/640, -253/640⟩, 3/1280⟩
def center2814 : GaussianRat :=
  ⟨-6970453/200000000, -289742037/1000000000⟩
def contact2814 : RatBall := localContactBall tau2814 center2814

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351


