-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0350
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0350
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:43:36.343974+00:00
-- url     : https://prove2.me/theorems/5360091e-5bd7-4d18-8e31-4c15be98d0f6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0350.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0350_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2804 : (center2804.re : ℝ)^2 +
    (center2804.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2804]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2804 : work2804.theta.ok = true ∧
    work2804.jac.invOK = true ∧ acceptsUnitSq work2804.out = true := by decide +kernel

def cell2804 : CellCertificate where
  tauBall := tau2804
  contactCenter := center2804
  contactBall := contact2804
  work := work2804
  center_sq := center_sq2804
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2804.1
  jac_ok := checks2804.2.1
  accepted := checks2804.2.2

def tau2805 : RatBall :=
  ⟨⟨-33/640, -247/640⟩, 3/1280⟩
def center2805 : GaussianRat :=
  ⟨-8438273/200000000, -281713577/1000000000⟩
def contact2805 : RatBall := localContactBall tau2805 center2805
def work2805 : RoundedTauEval :=
  evalTau precision tau2805 contact2805 logTwoBall

theorem center_sq2805 : (center2805.re : ℝ)^2 +
    (center2805.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2805]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2805 : work2805.theta.ok = true ∧
    work2805.jac.invOK = true ∧ acceptsUnitSq work2805.out = true := by decide +kernel

def cell2805 : CellCertificate where
  tauBall := tau2805
  contactCenter := center2805
  contactBall := contact2805
  work := work2805
  center_sq := center_sq2805
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2805.1
  jac_ok := checks2805.2.1
  accepted := checks2805.2.2

def tau2806 : RatBall :=
  ⟨⟨-7/128, -49/128⟩, 3/1280⟩
def center2806 : GaussianRat :=
  ⟨-44607937/1000000000, -279044067/1000000000⟩
def contact2806 : RatBall := localContactBall tau2806 center2806
def work2806 : RoundedTauEval :=
  evalTau precision tau2806 contact2806 logTwoBall

theorem center_sq2806 : (center2806.re : ℝ)^2 +
    (center2806.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2806]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2806 : work2806.theta.ok = true ∧
    work2806.jac.invOK = true ∧ acceptsUnitSq work2806.out = true := by decide +kernel

def cell2806 : CellCertificate where
  tauBall := tau2806
  contactCenter := center2806
  contactBall := contact2806
  work := work2806
  center_sq := center_sq2806
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2806.1
  jac_ok := checks2806.2.1
  accepted := checks2806.2.2

def tau2807 : RatBall :=
  ⟨⟨-33/640, -49/128⟩, 3/1280⟩
def center2807 : GaussianRat :=
  ⟨-42068541/1000000000, -27916967/100000000⟩
def contact2807 : RatBall := localContactBall tau2807 center2807
def work2807 : RoundedTauEval :=
  evalTau precision tau2807 contact2807 logTwoBall

theorem center_sq2807 : (center2807.re : ℝ)^2 +
    (center2807.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2807]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2807 : work2807.theta.ok = true ∧
    work2807.jac.invOK = true ∧ acceptsUnitSq work2807.out = true := by decide +kernel

def cell2807 : CellCertificate where
  tauBall := tau2807
  contactCenter := center2807
  contactBall := contact2807
  work := work2807
  center_sq := center_sq2807
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2807.1
  jac_ok := checks2807.2.1
  accepted := checks2807.2.2

def cells : List CellCertificate := [cell2800, cell2801, cell2802, cell2803, cell2804, cell2805, cell2806, cell2807]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350


