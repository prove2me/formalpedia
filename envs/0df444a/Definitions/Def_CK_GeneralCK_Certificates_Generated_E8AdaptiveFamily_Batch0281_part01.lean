-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0281_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0281_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:11:15.20552+00:00
-- url     : https://prove2.me/theorems/6eb84c06-5d38-4060-90f8-d52e289a402c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 2 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 2 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 2 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 2 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0281 (part 2 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0281_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2250 : RatBall :=
  ⟨⟨9/320, 23/64⟩, 3/640⟩
def center2250 : GaussianRat :=
  ⟨22499417/1000000000, 260954001/1000000000⟩
def contact2250 : RatBall := localContactBall tau2250 center2250
def work2250 : RoundedTauEval :=
  evalTau precision tau2250 contact2250 logTwoBall

theorem center_sq2250 : (center2250.re : ℝ)^2 +
    (center2250.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2250]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2250 : work2250.theta.ok = true ∧
    work2250.jac.invOK = true ∧ acceptsUnitSq work2250.out = true := by decide +kernel

def cell2250 : CellCertificate where
  tauBall := tau2250
  contactCenter := center2250
  contactBall := contact2250
  work := work2250
  center_sq := center_sq2250
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2250.1
  jac_ok := checks2250.2.1
  accepted := checks2250.2.2

def tau2251 : RatBall :=
  ⟨⟨11/320, 23/64⟩, 3/640⟩
def center2251 : GaussianRat :=
  ⟨27492413/1000000000, 2037657/7812500⟩
def contact2251 : RatBall := localContactBall tau2251 center2251
def work2251 : RoundedTauEval :=
  evalTau precision tau2251 contact2251 logTwoBall

theorem center_sq2251 : (center2251.re : ℝ)^2 +
    (center2251.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2251]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2251 : work2251.theta.ok = true ∧
    work2251.jac.invOK = true ∧ acceptsUnitSq work2251.out = true := by decide +kernel

def cell2251 : CellCertificate where
  tauBall := tau2251
  contactCenter := center2251
  contactBall := contact2251
  work := work2251
  center_sq := center_sq2251
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2251.1
  jac_ok := checks2251.2.1
  accepted := checks2251.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281


