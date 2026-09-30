-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0361
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0361
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:35:35.852798+00:00
-- url     : https://prove2.me/theorems/95a1eca8-80ac-4812-9b49-b6ca6072700d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0361.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0361_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2894 : RatBall :=
  ⟨⟨1/640, -249/640⟩, 3/1280⟩
def center2894 : GaussianRat :=
  ⟨1284711/1000000000, -285303029/1000000000⟩
def contact2894 : RatBall := localContactBall tau2894 center2894
def work2894 : RoundedTauEval :=
  evalTau precision tau2894 contact2894 logTwoBall

theorem center_sq2894 : (center2894.re : ℝ)^2 +
    (center2894.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2894]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2894 : work2894.theta.ok = true ∧
    work2894.jac.invOK = true ∧ acceptsUnitSq work2894.out = true := by decide +kernel

def cell2894 : CellCertificate where
  tauBall := tau2894
  contactCenter := center2894
  contactBall := contact2894
  work := work2894
  center_sq := center_sq2894
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2894.1
  jac_ok := checks2894.2.1
  accepted := checks2894.2.2

def tau2895 : RatBall :=
  ⟨⟨3/640, -249/640⟩, 3/1280⟩
def center2895 : GaussianRat :=
  ⟨3854079/1000000000, -142647681/500000000⟩
def contact2895 : RatBall := localContactBall tau2895 center2895
def work2895 : RoundedTauEval :=
  evalTau precision tau2895 contact2895 logTwoBall

theorem center_sq2895 : (center2895.re : ℝ)^2 +
    (center2895.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2895]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2895 : work2895.theta.ok = true ∧
    work2895.jac.invOK = true ∧ acceptsUnitSq work2895.out = true := by decide +kernel

def cell2895 : CellCertificate where
  tauBall := tau2895
  contactCenter := center2895
  contactBall := contact2895
  work := work2895
  center_sq := center_sq2895
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2895.1
  jac_ok := checks2895.2.1
  accepted := checks2895.2.2

def cells : List CellCertificate := [cell2888, cell2889, cell2890, cell2891, cell2892, cell2893, cell2894, cell2895]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361


