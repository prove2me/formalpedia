-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0307
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0307
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:41:11.028216+00:00
-- url     : https://prove2.me/theorems/e625f524-ed7c-4187-9f81-baf4a674c069
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0307.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0307_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell2461 : CellCertificate where
  tauBall := tau2461
  contactCenter := center2461
  contactBall := contact2461
  work := work2461
  center_sq := center_sq2461
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2461.1
  jac_ok := checks2461.2.1
  accepted := checks2461.2.2

def tau2462 : RatBall :=
  ⟨⟨93/320, 83/320⟩, 3/640⟩
def center2462 : GaussianRat :=
  ⟨52110811/250000000, 167692033/1000000000⟩
def contact2462 : RatBall := localContactBall tau2462 center2462
def work2462 : RoundedTauEval :=
  evalTau precision tau2462 contact2462 logTwoBall

theorem center_sq2462 : (center2462.re : ℝ)^2 +
    (center2462.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2462]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2462 : work2462.theta.ok = true ∧
    work2462.jac.invOK = true ∧ acceptsUnitSq work2462.out = true := by decide +kernel

def cell2462 : CellCertificate where
  tauBall := tau2462
  contactCenter := center2462
  contactBall := contact2462
  work := work2462
  center_sq := center_sq2462
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2462.1
  jac_ok := checks2462.2.1
  accepted := checks2462.2.2

def tau2463 : RatBall :=
  ⟨⟨19/64, 83/320⟩, 3/640⟩
def center2463 : GaussianRat :=
  ⟨212592873/1000000000, 33409337/200000000⟩
def contact2463 : RatBall := localContactBall tau2463 center2463
def work2463 : RoundedTauEval :=
  evalTau precision tau2463 contact2463 logTwoBall

theorem center_sq2463 : (center2463.re : ℝ)^2 +
    (center2463.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2463]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2463 : work2463.theta.ok = true ∧
    work2463.jac.invOK = true ∧ acceptsUnitSq work2463.out = true := by decide +kernel

def cell2463 : CellCertificate where
  tauBall := tau2463
  contactCenter := center2463
  contactBall := contact2463
  work := work2463
  center_sq := center_sq2463
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2463.1
  jac_ok := checks2463.2.1
  accepted := checks2463.2.2

def cells : List CellCertificate := [cell2456, cell2457, cell2458, cell2459, cell2460, cell2461, cell2462, cell2463]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307


