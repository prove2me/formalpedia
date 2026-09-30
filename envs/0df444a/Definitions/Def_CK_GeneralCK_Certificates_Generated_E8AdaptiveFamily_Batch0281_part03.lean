-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0281_part03
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0281_part03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:54:10.021226+00:00
-- url     : https://prove2.me/theorems/4e61aa00-7e6a-4f47-834d-ce7a74a09992
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 4 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 4 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 4 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 4 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0281 (part 4 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0281_part02

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2254 : RatBall :=
  ⟨⟨13/320, 23/64⟩, 3/640⟩
def center2254 : GaussianRat :=
  ⟨32481297/1000000000, 260659621/1000000000⟩
def contact2254 : RatBall := localContactBall tau2254 center2254
def work2254 : RoundedTauEval :=
  evalTau precision tau2254 contact2254 logTwoBall

theorem center_sq2254 : (center2254.re : ℝ)^2 +
    (center2254.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2254]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2254 : work2254.theta.ok = true ∧
    work2254.jac.invOK = true ∧ acceptsUnitSq work2254.out = true := by decide +kernel

def cell2254 : CellCertificate where
  tauBall := tau2254
  contactCenter := center2254
  contactBall := contact2254
  work := work2254
  center_sq := center_sq2254
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2254.1
  jac_ok := checks2254.2.1
  accepted := checks2254.2.2

def tau2255 : RatBall :=
  ⟨⟨3/64, 23/64⟩, 3/640⟩
def center2255 : GaussianRat :=
  ⟨37465331/1000000000, 260472693/1000000000⟩
def contact2255 : RatBall := localContactBall tau2255 center2255
def work2255 : RoundedTauEval :=
  evalTau precision tau2255 contact2255 logTwoBall

theorem center_sq2255 : (center2255.re : ℝ)^2 +
    (center2255.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2255]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2255 : work2255.theta.ok = true ∧
    work2255.jac.invOK = true ∧ acceptsUnitSq work2255.out = true := by decide +kernel

def cell2255 : CellCertificate where
  tauBall := tau2255
  contactCenter := center2255
  contactBall := contact2255
  work := work2255
  center_sq := center_sq2255
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2255.1
  jac_ok := checks2255.2.1
  accepted := checks2255.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281


