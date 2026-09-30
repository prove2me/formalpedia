-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0347
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0347
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:55:18.974972+00:00
-- url     : https://prove2.me/theorems/625c0109-7605-4deb-ae79-37733fa2f9c0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0347` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0347` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0347` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0347 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0347.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0347_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0347

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact2782 : RatBall := localContactBall tau2782 center2782
def work2782 : RoundedTauEval :=
  evalTau precision tau2782 contact2782 logTwoBall

theorem center_sq2782 : (center2782.re : ℝ)^2 +
    (center2782.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2782]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2782 : work2782.theta.ok = true ∧
    work2782.jac.invOK = true ∧ acceptsUnitSq work2782.out = true := by decide +kernel

def cell2782 : CellCertificate where
  tauBall := tau2782
  contactCenter := center2782
  contactBall := contact2782
  work := work2782
  center_sq := center_sq2782
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2782.1
  jac_ok := checks2782.2.1
  accepted := checks2782.2.2

def tau2783 : RatBall :=
  ⟨⟨-37/640, -249/640⟩, 3/1280⟩
def center2783 : GaussianRat :=
  ⟨-11855567/250000000, -283999143/1000000000⟩
def contact2783 : RatBall := localContactBall tau2783 center2783
def work2783 : RoundedTauEval :=
  evalTau precision tau2783 contact2783 logTwoBall

theorem center_sq2783 : (center2783.re : ℝ)^2 +
    (center2783.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2783]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2783 : work2783.theta.ok = true ∧
    work2783.jac.invOK = true ∧ acceptsUnitSq work2783.out = true := by decide +kernel

def cell2783 : CellCertificate where
  tauBall := tau2783
  contactCenter := center2783
  contactBall := contact2783
  work := work2783
  center_sq := center_sq2783
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2783.1
  jac_ok := checks2783.2.1
  accepted := checks2783.2.2

def cells : List CellCertificate := [cell2776, cell2777, cell2778, cell2779, cell2780, cell2781, cell2782, cell2783]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0347


