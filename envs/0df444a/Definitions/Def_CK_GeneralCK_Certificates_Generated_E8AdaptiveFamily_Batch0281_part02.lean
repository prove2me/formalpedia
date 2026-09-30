-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0281_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0281_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:19:30.967803+00:00
-- url     : https://prove2.me/theorems/28d41b3f-9dde-4933-ac13-50673fdfa1c6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 3 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 3 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 3 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 3 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0281 (part 3 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0281_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2252 : RatBall :=
  ⟨⟨13/320, 113/320⟩, 3/640⟩
def center2252 : GaussianRat :=
  ⟨32309979/1000000000, 127843073/500000000⟩
def contact2252 : RatBall := localContactBall tau2252 center2252
def work2252 : RoundedTauEval :=
  evalTau precision tau2252 contact2252 logTwoBall

theorem center_sq2252 : (center2252.re : ℝ)^2 +
    (center2252.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2252]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2252 : work2252.theta.ok = true ∧
    work2252.jac.invOK = true ∧ acceptsUnitSq work2252.out = true := by decide +kernel

def cell2252 : CellCertificate where
  tauBall := tau2252
  contactCenter := center2252
  contactBall := contact2252
  work := work2252
  center_sq := center_sq2252
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2252.1
  jac_ok := checks2252.2.1
  accepted := checks2252.2.2

def tau2253 : RatBall :=
  ⟨⟨3/64, 113/320⟩, 3/640⟩
def center2253 : GaussianRat :=
  ⟨18633993/500000000, 15969023/62500000⟩
def contact2253 : RatBall := localContactBall tau2253 center2253
def work2253 : RoundedTauEval :=
  evalTau precision tau2253 contact2253 logTwoBall

theorem center_sq2253 : (center2253.re : ℝ)^2 +
    (center2253.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2253]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2253 : work2253.theta.ok = true ∧
    work2253.jac.invOK = true ∧ acceptsUnitSq work2253.out = true := by decide +kernel

def cell2253 : CellCertificate where
  tauBall := tau2253
  contactCenter := center2253
  contactBall := contact2253
  work := work2253
  center_sq := center_sq2253
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2253.1
  jac_ok := checks2253.2.1
  accepted := checks2253.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281


