-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0341
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0341
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:07:25.872944+00:00
-- url     : https://prove2.me/theorems/74df562c-bab2-4b16-a6ef-d5f8b8bac474
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0341.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0341_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2732 : (center2732.re : ℝ)^2 +
    (center2732.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2732]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2732 : work2732.theta.ok = true ∧
    work2732.jac.invOK = true ∧ acceptsUnitSq work2732.out = true := by decide +kernel

def cell2732 : CellCertificate where
  tauBall := tau2732
  contactCenter := center2732
  contactBall := contact2732
  work := work2732
  center_sq := center_sq2732
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2732.1
  jac_ok := checks2732.2.1
  accepted := checks2732.2.2

def tau2733 : RatBall :=
  ⟨⟨-63/640, -247/640⟩, 3/1280⟩
def center2733 : GaussianRat :=
  ⟨-40078273/500000000, -69761453/250000000⟩
def contact2733 : RatBall := localContactBall tau2733 center2733
def work2733 : RoundedTauEval :=
  evalTau precision tau2733 contact2733 logTwoBall

theorem center_sq2733 : (center2733.re : ℝ)^2 +
    (center2733.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2733]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2733 : work2733.theta.ok = true ∧
    work2733.jac.invOK = true ∧ acceptsUnitSq work2733.out = true := by decide +kernel

def cell2733 : CellCertificate where
  tauBall := tau2733
  contactCenter := center2733
  contactBall := contact2733
  work := work2733
  center_sq := center_sq2733
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2733.1
  jac_ok := checks2733.2.1
  accepted := checks2733.2.2

def tau2734 : RatBall :=
  ⟨⟨-61/640, -247/640⟩, 3/1280⟩
def center2734 : GaussianRat :=
  ⟨-77644141/1000000000, -139636577/500000000⟩
def contact2734 : RatBall := localContactBall tau2734 center2734
def work2734 : RoundedTauEval :=
  evalTau precision tau2734 contact2734 logTwoBall

theorem center_sq2734 : (center2734.re : ℝ)^2 +
    (center2734.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2734]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2734 : work2734.theta.ok = true ∧
    work2734.jac.invOK = true ∧ acceptsUnitSq work2734.out = true := by decide +kernel

def cell2734 : CellCertificate where
  tauBall := tau2734
  contactCenter := center2734
  contactBall := contact2734
  work := work2734
  center_sq := center_sq2734
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2734.1
  jac_ok := checks2734.2.1
  accepted := checks2734.2.2

def tau2735 : RatBall :=
  ⟨⟨-63/640, -49/128⟩, 3/1280⟩
def center2735 : GaussianRat :=
  ⟨-39963667/500000000, -276538391/1000000000⟩
def contact2735 : RatBall := localContactBall tau2735 center2735
def work2735 : RoundedTauEval :=
  evalTau precision tau2735 contact2735 logTwoBall

theorem center_sq2735 : (center2735.re : ℝ)^2 +
    (center2735.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2735]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2735 : work2735.theta.ok = true ∧
    work2735.jac.invOK = true ∧ acceptsUnitSq work2735.out = true := by decide +kernel

def cell2735 : CellCertificate where
  tauBall := tau2735
  contactCenter := center2735
  contactBall := contact2735
  work := work2735
  center_sq := center_sq2735
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2735.1
  jac_ok := checks2735.2.1
  accepted := checks2735.2.2

def cells : List CellCertificate := [cell2728, cell2729, cell2730, cell2731, cell2732, cell2733, cell2734, cell2735]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341


