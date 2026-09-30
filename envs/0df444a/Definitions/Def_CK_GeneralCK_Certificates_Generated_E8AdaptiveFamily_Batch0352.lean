-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0352
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0352
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:03:22.312395+00:00
-- url     : https://prove2.me/theorems/58636d1f-3c85-498e-b84e-9e841f5c3e1d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0352.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0352_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2821 : work2821.theta.ok = true ∧
    work2821.jac.invOK = true ∧ acceptsUnitSq work2821.out = true := by decide +kernel

def cell2821 : CellCertificate where
  tauBall := tau2821
  contactCenter := center2821
  contactBall := contact2821
  work := work2821
  center_sq := center_sq2821
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2821.1
  jac_ok := checks2821.2.1
  accepted := checks2821.2.2

def tau2822 : RatBall :=
  ⟨⟨-27/640, -249/640⟩, 3/1280⟩
def center2822 : GaussianRat :=
  ⟨-34643579/1000000000, -56921471/200000000⟩
def contact2822 : RatBall := localContactBall tau2822 center2822
def work2822 : RoundedTauEval :=
  evalTau precision tau2822 contact2822 logTwoBall

theorem center_sq2822 : (center2822.re : ℝ)^2 +
    (center2822.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2822]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2822 : work2822.theta.ok = true ∧
    work2822.jac.invOK = true ∧ acceptsUnitSq work2822.out = true := by decide +kernel

def cell2822 : CellCertificate where
  tauBall := tau2822
  contactCenter := center2822
  contactBall := contact2822
  work := work2822
  center_sq := center_sq2822
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2822.1
  jac_ok := checks2822.2.1
  accepted := checks2822.2.2

def tau2823 : RatBall :=
  ⟨⟨-5/128, -249/640⟩, 3/1280⟩
def center2823 : GaussianRat :=
  ⟨-32083143/1000000000, -142353243/500000000⟩
def contact2823 : RatBall := localContactBall tau2823 center2823
def work2823 : RoundedTauEval :=
  evalTau precision tau2823 contact2823 logTwoBall

theorem center_sq2823 : (center2823.re : ℝ)^2 +
    (center2823.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2823]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2823 : work2823.theta.ok = true ∧
    work2823.jac.invOK = true ∧ acceptsUnitSq work2823.out = true := by decide +kernel

def cell2823 : CellCertificate where
  tauBall := tau2823
  contactCenter := center2823
  contactBall := contact2823
  work := work2823
  center_sq := center_sq2823
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2823.1
  jac_ok := checks2823.2.1
  accepted := checks2823.2.2

def cells : List CellCertificate := [cell2816, cell2817, cell2818, cell2819, cell2820, cell2821, cell2822, cell2823]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352


