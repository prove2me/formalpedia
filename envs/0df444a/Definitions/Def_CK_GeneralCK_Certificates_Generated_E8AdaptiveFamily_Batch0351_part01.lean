-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0351_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0351_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:17:04.025076+00:00
-- url     : https://prove2.me/theorems/aaf67735-cca1-4e06-9180-99238e723a41
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0351 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0351_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center2810 : GaussianRat :=
  ⟨-9999803/250000000, -36189373/125000000⟩
def contact2810 : RatBall := localContactBall tau2810 center2810
def work2810 : RoundedTauEval :=
  evalTau precision tau2810 contact2810 logTwoBall

theorem center_sq2810 : (center2810.re : ℝ)^2 +
    (center2810.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2810]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2810 : work2810.theta.ok = true ∧
    work2810.jac.invOK = true ∧ acceptsUnitSq work2810.out = true := by decide +kernel

def cell2810 : CellCertificate where
  tauBall := tau2810
  contactCenter := center2810
  contactBall := contact2810
  work := work2810
  center_sq := center_sq2810
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2810.1
  jac_ok := checks2810.2.1
  accepted := checks2810.2.2

def tau2811 : RatBall :=
  ⟨⟨-29/640, -253/640⟩, 3/1280⟩
def center2811 : GaussianRat :=
  ⟨-18713263/500000000, -289632371/1000000000⟩
def contact2811 : RatBall := localContactBall tau2811 center2811
def work2811 : RoundedTauEval :=
  evalTau precision tau2811 contact2811 logTwoBall

theorem center_sq2811 : (center2811.re : ℝ)^2 +
    (center2811.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2811]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2811 : work2811.theta.ok = true ∧
    work2811.jac.invOK = true ∧ acceptsUnitSq work2811.out = true := by decide +kernel

def cell2811 : CellCertificate where
  tauBall := tau2811
  contactCenter := center2811
  contactBall := contact2811
  work := work2811
  center_sq := center_sq2811
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2811.1
  jac_ok := checks2811.2.1
  accepted := checks2811.2.2

def tau2812 : RatBall :=
  ⟨⟨-27/640, -51/128⟩, 3/1280⟩
def center2812 : GaussianRat :=
  ⟨-34958801/1000000000, -14616047/50000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351


