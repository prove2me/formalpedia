-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0366
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0366
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:54:15.148978+00:00
-- url     : https://prove2.me/theorems/fb73c93d-be94-42dc-8b9e-e152600f69c9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0366` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0366` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0366` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0366 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0366.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0366_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0366

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work2934 : RoundedTauEval :=
  evalTau precision tau2934 contact2934 logTwoBall

theorem center_sq2934 : (center2934.re : ℝ)^2 +
    (center2934.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2934]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2934 : work2934.theta.ok = true ∧
    work2934.jac.invOK = true ∧ acceptsUnitSq work2934.out = true := by decide +kernel

def cell2934 : CellCertificate where
  tauBall := tau2934
  contactCenter := center2934
  contactBall := contact2934
  work := work2934
  center_sq := center_sq2934
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2934.1
  jac_ok := checks2934.2.1
  accepted := checks2934.2.2

def tau2935 : RatBall :=
  ⟨⟨27/640, -253/640⟩, 3/1280⟩
def center2935 : GaussianRat :=
  ⟨6970453/200000000, -289742037/1000000000⟩
def contact2935 : RatBall := localContactBall tau2935 center2935
def work2935 : RoundedTauEval :=
  evalTau precision tau2935 contact2935 logTwoBall

theorem center_sq2935 : (center2935.re : ℝ)^2 +
    (center2935.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2935]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2935 : work2935.theta.ok = true ∧
    work2935.jac.invOK = true ∧ acceptsUnitSq work2935.out = true := by decide +kernel

def cell2935 : CellCertificate where
  tauBall := tau2935
  contactCenter := center2935
  contactBall := contact2935
  work := work2935
  center_sq := center_sq2935
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2935.1
  jac_ok := checks2935.2.1
  accepted := checks2935.2.2

def cells : List CellCertificate := [cell2928, cell2929, cell2930, cell2931, cell2932, cell2933, cell2934, cell2935]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0366


