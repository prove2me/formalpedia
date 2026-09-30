-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0294
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0294
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:27:39.953854+00:00
-- url     : https://prove2.me/theorems/5c040e24-0dfd-47c7-86f0-43ba377102a8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0294.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0294_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell2357 : CellCertificate where
  tauBall := tau2357
  contactCenter := center2357
  contactBall := contact2357
  work := work2357
  center_sq := center_sq2357
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2357.1
  jac_ok := checks2357.2.1
  accepted := checks2357.2.2

def tau2358 : RatBall :=
  ⟨⟨61/320, 99/320⟩, 3/640⟩
def center2358 : GaussianRat :=
  ⟨28778703/200000000, 106261649/500000000⟩
def contact2358 : RatBall := localContactBall tau2358 center2358
def work2358 : RoundedTauEval :=
  evalTau precision tau2358 contact2358 logTwoBall

theorem center_sq2358 : (center2358.re : ℝ)^2 +
    (center2358.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2358]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2358 : work2358.theta.ok = true ∧
    work2358.jac.invOK = true ∧ acceptsUnitSq work2358.out = true := by decide +kernel

def cell2358 : CellCertificate where
  tauBall := tau2358
  contactCenter := center2358
  contactBall := contact2358
  work := work2358
  center_sq := center_sq2358
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2358.1
  jac_ok := checks2358.2.1
  accepted := checks2358.2.2

def tau2359 : RatBall :=
  ⟨⟨63/320, 99/320⟩, 3/640⟩
def center2359 : GaussianRat :=
  ⟨148426041/1000000000, 105961569/500000000⟩
def contact2359 : RatBall := localContactBall tau2359 center2359
def work2359 : RoundedTauEval :=
  evalTau precision tau2359 contact2359 logTwoBall

theorem center_sq2359 : (center2359.re : ℝ)^2 +
    (center2359.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2359]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2359 : work2359.theta.ok = true ∧
    work2359.jac.invOK = true ∧ acceptsUnitSq work2359.out = true := by decide +kernel

def cell2359 : CellCertificate where
  tauBall := tau2359
  contactCenter := center2359
  contactBall := contact2359
  work := work2359
  center_sq := center_sq2359
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2359.1
  jac_ok := checks2359.2.1
  accepted := checks2359.2.2

def cells : List CellCertificate := [cell2352, cell2353, cell2354, cell2355, cell2356, cell2357, cell2358, cell2359]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294


