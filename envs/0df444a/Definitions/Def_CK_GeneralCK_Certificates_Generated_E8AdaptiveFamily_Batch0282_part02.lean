-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0282_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0282_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:03:43.432112+00:00
-- url     : https://prove2.me/theorems/92147f28-43e2-4183-9dbb-dc3c22faeeee
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0282 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0282_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact2260 : RatBall := localContactBall tau2260 center2260
def work2260 : RoundedTauEval :=
  evalTau precision tau2260 contact2260 logTwoBall

theorem center_sq2260 : (center2260.re : ℝ)^2 +
    (center2260.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2260]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2260 : work2260.theta.ok = true ∧
    work2260.jac.invOK = true ∧ acceptsUnitSq work2260.out = true := by decide +kernel

def cell2260 : CellCertificate where
  tauBall := tau2260
  contactCenter := center2260
  contactBall := contact2260
  work := work2260
  center_sq := center_sq2260
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2260.1
  jac_ok := checks2260.2.1
  accepted := checks2260.2.2

def tau2261 : RatBall :=
  ⟨⟨3/64, 117/320⟩, 3/640⟩
def center2261 : GaussianRat :=
  ⟨18834129/500000000, 13273367/50000000⟩
def contact2261 : RatBall := localContactBall tau2261 center2261
def work2261 : RoundedTauEval :=
  evalTau precision tau2261 contact2261 logTwoBall

theorem center_sq2261 : (center2261.re : ℝ)^2 +
    (center2261.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2261]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2261 : work2261.theta.ok = true ∧
    work2261.jac.invOK = true ∧ acceptsUnitSq work2261.out = true := by decide +kernel

def cell2261 : CellCertificate where
  tauBall := tau2261
  contactCenter := center2261
  contactBall := contact2261
  work := work2261
  center_sq := center_sq2261
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2261.1
  jac_ok := checks2261.2.1
  accepted := checks2261.2.2

def tau2262 : RatBall :=
  ⟨⟨13/320, 119/320⟩, 3/640⟩
def center2262 : GaussianRat :=
  ⟨32838611/1000000000, 135343343/500000000⟩
def contact2262 : RatBall := localContactBall tau2262 center2262

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282


