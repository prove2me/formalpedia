-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0360
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0360
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:29:49.369519+00:00
-- url     : https://prove2.me/theorems/da24e195-3845-45c7-86d3-3350bb0618e6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0360.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0360_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work2885 : RoundedTauEval :=
  evalTau precision tau2885 contact2885 logTwoBall

theorem center_sq2885 : (center2885.re : ℝ)^2 +
    (center2885.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2885]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2885 : work2885.theta.ok = true ∧
    work2885.jac.invOK = true ∧ acceptsUnitSq work2885.out = true := by decide +kernel

def cell2885 : CellCertificate where
  tauBall := tau2885
  contactCenter := center2885
  contactBall := contact2885
  work := work2885
  center_sq := center_sq2885
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2885.1
  jac_ok := checks2885.2.1
  accepted := checks2885.2.2

def tau2886 : RatBall :=
  ⟨⟨1/640, -253/640⟩, 3/1280⟩
def center2886 : GaussianRat :=
  ⟨646243/500000000, -72614333/250000000⟩
def contact2886 : RatBall := localContactBall tau2886 center2886
def work2886 : RoundedTauEval :=
  evalTau precision tau2886 contact2886 logTwoBall

theorem center_sq2886 : (center2886.re : ℝ)^2 +
    (center2886.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2886]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2886 : work2886.theta.ok = true ∧
    work2886.jac.invOK = true ∧ acceptsUnitSq work2886.out = true := by decide +kernel

def cell2886 : CellCertificate where
  tauBall := tau2886
  contactCenter := center2886
  contactBall := contact2886
  work := work2886
  center_sq := center_sq2886
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2886.1
  jac_ok := checks2886.2.1
  accepted := checks2886.2.2

def tau2887 : RatBall :=
  ⟨⟨3/640, -253/640⟩, 3/1280⟩
def center2887 : GaussianRat :=
  ⟨3877403/1000000000, -36306181/125000000⟩
def contact2887 : RatBall := localContactBall tau2887 center2887
def work2887 : RoundedTauEval :=
  evalTau precision tau2887 contact2887 logTwoBall

theorem center_sq2887 : (center2887.re : ℝ)^2 +
    (center2887.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2887]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2887 : work2887.theta.ok = true ∧
    work2887.jac.invOK = true ∧ acceptsUnitSq work2887.out = true := by decide +kernel

def cell2887 : CellCertificate where
  tauBall := tau2887
  contactCenter := center2887
  contactBall := contact2887
  work := work2887
  center_sq := center_sq2887
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2887.1
  jac_ok := checks2887.2.1
  accepted := checks2887.2.2

def cells : List CellCertificate := [cell2880, cell2881, cell2882, cell2883, cell2884, cell2885, cell2886, cell2887]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360


