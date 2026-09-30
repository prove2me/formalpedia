-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0268
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0268
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:33:12.663979+00:00
-- url     : https://prove2.me/theorems/167be1b5-28cd-471c-a0bd-e711052184d1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0268` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0268` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0268` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0268 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0268.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0268_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0268

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work2150 : RoundedTauEval :=
  evalTau precision tau2150 contact2150 logTwoBall

theorem center_sq2150 : (center2150.re : ℝ)^2 +
    (center2150.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2150]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2150 : work2150.theta.ok = true ∧
    work2150.jac.invOK = true ∧ acceptsUnitSq work2150.out = true := by decide +kernel

def cell2150 : CellCertificate where
  tauBall := tau2150
  contactCenter := center2150
  contactBall := contact2150
  work := work2150
  center_sq := center_sq2150
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2150.1
  jac_ok := checks2150.2.1
  accepted := checks2150.2.2

def tau2151 : RatBall :=
  ⟨⟨-27/320, 113/320⟩, 3/640⟩
def center2151 : GaussianRat :=
  ⟨-33438609/500000000, 253881789/1000000000⟩
def contact2151 : RatBall := localContactBall tau2151 center2151
def work2151 : RoundedTauEval :=
  evalTau precision tau2151 contact2151 logTwoBall

theorem center_sq2151 : (center2151.re : ℝ)^2 +
    (center2151.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2151]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2151 : work2151.theta.ok = true ∧
    work2151.jac.invOK = true ∧ acceptsUnitSq work2151.out = true := by decide +kernel

def cell2151 : CellCertificate where
  tauBall := tau2151
  contactCenter := center2151
  contactBall := contact2151
  work := work2151
  center_sq := center_sq2151
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2151.1
  jac_ok := checks2151.2.1
  accepted := checks2151.2.2

def cells : List CellCertificate := [cell2144, cell2145, cell2146, cell2147, cell2148, cell2149, cell2150, cell2151]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0268


