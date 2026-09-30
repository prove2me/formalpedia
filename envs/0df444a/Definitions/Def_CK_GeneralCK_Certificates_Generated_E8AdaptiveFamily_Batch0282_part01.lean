-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0282_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0282_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:20:26.01158+00:00
-- url     : https://prove2.me/theorems/a6485875-366a-42d0-821c-8702347e243b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0282 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0282_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center2258 : GaussianRat :=
  ⟨22747453/1000000000, 270997951/1000000000⟩
def contact2258 : RatBall := localContactBall tau2258 center2258
def work2258 : RoundedTauEval :=
  evalTau precision tau2258 contact2258 logTwoBall

theorem center_sq2258 : (center2258.re : ℝ)^2 +
    (center2258.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2258]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2258 : work2258.theta.ok = true ∧
    work2258.jac.invOK = true ∧ acceptsUnitSq work2258.out = true := by decide +kernel

def cell2258 : CellCertificate where
  tauBall := tau2258
  contactCenter := center2258
  contactBall := contact2258
  work := work2258
  center_sq := center_sq2258
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2258.1
  jac_ok := checks2258.2.1
  accepted := checks2258.2.2

def tau2259 : RatBall :=
  ⟨⟨11/320, 119/320⟩, 3/640⟩
def center2259 : GaussianRat :=
  ⟨27795199/1000000000, 135428181/500000000⟩
def contact2259 : RatBall := localContactBall tau2259 center2259
def work2259 : RoundedTauEval :=
  evalTau precision tau2259 contact2259 logTwoBall

theorem center_sq2259 : (center2259.re : ℝ)^2 +
    (center2259.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2259]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2259 : work2259.theta.ok = true ∧
    work2259.jac.invOK = true ∧ acceptsUnitSq work2259.out = true := by decide +kernel

def cell2259 : CellCertificate where
  tauBall := tau2259
  contactCenter := center2259
  contactBall := contact2259
  work := work2259
  center_sq := center_sq2259
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2259.1
  jac_ok := checks2259.2.1
  accepted := checks2259.2.2

def tau2260 : RatBall :=
  ⟨⟨13/320, 117/320⟩, 3/640⟩
def center2260 : GaussianRat :=
  ⟨6531493/200000000, 265659553/1000000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282


