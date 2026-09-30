-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0356
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0356
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:19:29.98524+00:00
-- url     : https://prove2.me/theorems/cbd994dd-8aca-42cb-b7f9-004de9b2712c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0356.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0356_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work2853 : RoundedTauEval :=
  evalTau precision tau2853 contact2853 logTwoBall

theorem center_sq2853 : (center2853.re : ℝ)^2 +
    (center2853.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2853]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2853 : work2853.theta.ok = true ∧
    work2853.jac.invOK = true ∧ acceptsUnitSq work2853.out = true := by decide +kernel

def cell2853 : CellCertificate where
  tauBall := tau2853
  contactCenter := center2853
  contactBall := contact2853
  work := work2853
  center_sq := center_sq2853
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2853.1
  jac_ok := checks2853.2.1
  accepted := checks2853.2.2

def tau2854 : RatBall :=
  ⟨⟨-3/128, -253/640⟩, 3/1280⟩
def center2854 : GaussianRat :=
  ⟨-19379607/1000000000, -58047357/200000000⟩
def contact2854 : RatBall := localContactBall tau2854 center2854
def work2854 : RoundedTauEval :=
  evalTau precision tau2854 contact2854 logTwoBall

theorem center_sq2854 : (center2854.re : ℝ)^2 +
    (center2854.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2854]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2854 : work2854.theta.ok = true ∧
    work2854.jac.invOK = true ∧ acceptsUnitSq work2854.out = true := by decide +kernel

def cell2854 : CellCertificate where
  tauBall := tau2854
  contactCenter := center2854
  contactBall := contact2854
  work := work2854
  center_sq := center_sq2854
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2854.1
  jac_ok := checks2854.2.1
  accepted := checks2854.2.2

def tau2855 : RatBall :=
  ⟨⟨-13/640, -253/640⟩, 3/1280⟩
def center2855 : GaussianRat :=
  ⟨-16797323/1000000000, -290291883/1000000000⟩
def contact2855 : RatBall := localContactBall tau2855 center2855
def work2855 : RoundedTauEval :=
  evalTau precision tau2855 contact2855 logTwoBall

theorem center_sq2855 : (center2855.re : ℝ)^2 +
    (center2855.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2855]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2855 : work2855.theta.ok = true ∧
    work2855.jac.invOK = true ∧ acceptsUnitSq work2855.out = true := by decide +kernel

def cell2855 : CellCertificate where
  tauBall := tau2855
  contactCenter := center2855
  contactBall := contact2855
  work := work2855
  center_sq := center_sq2855
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2855.1
  jac_ok := checks2855.2.1
  accepted := checks2855.2.2

def cells : List CellCertificate := [cell2848, cell2849, cell2850, cell2851, cell2852, cell2853, cell2854, cell2855]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356


