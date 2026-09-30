-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0322
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0322
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:28:52.114455+00:00
-- url     : https://prove2.me/theorems/722ae107-1f15-4ef3-8ab6-725d28a4739f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0322` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0322` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0322` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0322 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0322.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0322 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0322

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2576 : RatBall :=
  ⟨⟨-141/640, -43/128⟩, 3/1280⟩
def center2576 : GaussianRat :=
  ⟨-84129393/500000000, -228617923/1000000000⟩
def contact2576 : RatBall := localContactBall tau2576 center2576
def work2576 : RoundedTauEval :=
  evalTau precision tau2576 contact2576 logTwoBall

theorem center_sq2576 : (center2576.re : ℝ)^2 +
    (center2576.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2576]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2576 : work2576.theta.ok = true ∧
    work2576.jac.invOK = true ∧ acceptsUnitSq work2576.out = true := by decide +kernel

def cell2576 : CellCertificate where
  tauBall := tau2576
  contactCenter := center2576
  contactBall := contact2576
  work := work2576
  center_sq := center_sq2576
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2576.1
  jac_ok := checks2576.2.1
  accepted := checks2576.2.2

def tau2577 : RatBall :=
  ⟨⟨-143/640, -213/640⟩, 3/1280⟩
def center2577 : GaussianRat :=
  ⟨-85071813/500000000, -28248739/125000000⟩
def contact2577 : RatBall := localContactBall tau2577 center2577
def work2577 : RoundedTauEval :=
  evalTau precision tau2577 contact2577 logTwoBall

theorem center_sq2577 : (center2577.re : ℝ)^2 +
    (center2577.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2577]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2577 : work2577.theta.ok = true ∧
    work2577.jac.invOK = true ∧ acceptsUnitSq work2577.out = true := by decide +kernel

def cell2577 : CellCertificate where
  tauBall := tau2577
  contactCenter := center2577
  contactBall := contact2577
  work := work2577
  center_sq := center_sq2577
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2577.1
  jac_ok := checks2577.2.1
  accepted := checks2577.2.2

def tau2578 : RatBall :=
  ⟨⟨-141/640, -213/640⟩, 3/1280⟩
def center2578 : GaussianRat :=
  ⟨-33577827/200000000, -28294879/125000000⟩
def contact2578 : RatBall := localContactBall tau2578 center2578
def work2578 : RoundedTauEval :=
  evalTau precision tau2578 contact2578 logTwoBall

theorem center_sq2578 : (center2578.re : ℝ)^2 +
    (center2578.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2578]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2578 : work2578.theta.ok = true ∧
    work2578.jac.invOK = true ∧ acceptsUnitSq work2578.out = true := by decide +kernel

def cell2578 : CellCertificate where
  tauBall := tau2578
  contactCenter := center2578
  contactBall := contact2578
  work := work2578
  center_sq := center_sq2578
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2578.1
  jac_ok := checks2578.2.1
  accepted := checks2578.2.2

def tau2579 : RatBall :=
  ⟨⟨-121/640, -227/640⟩, 3/1280⟩
def center2579 : GaussianRat :=
  ⟨-147475889/1000000000, -123032099/500000000⟩
def contact2579 : RatBall := localContactBall tau2579 center2579
def work2579 : RoundedTauEval :=
  evalTau precision tau2579 contact2579 logTwoBall

theorem center_sq2579 : (center2579.re : ℝ)^2 +
    (center2579.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2579]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2579 : work2579.theta.ok = true ∧
    work2579.jac.invOK = true ∧ acceptsUnitSq work2579.out = true := by decide +kernel

def cell2579 : CellCertificate where
  tauBall := tau2579
  contactCenter := center2579
  contactBall := contact2579
  work := work2579
  center_sq := center_sq2579
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2579.1
  jac_ok := checks2579.2.1
  accepted := checks2579.2.2

def tau2580 : RatBall :=
  ⟨⟨-123/640, -45/128⟩, 3/1280⟩
def center2580 : GaussianRat :=
  ⟨-149448351/1000000000, -9735017/40000000⟩
def contact2580 : RatBall := localContactBall tau2580 center2580
def work2580 : RoundedTauEval :=
  evalTau precision tau2580 contact2580 logTwoBall

theorem center_sq2580 : (center2580.re : ℝ)^2 +
    (center2580.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2580]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2580 : work2580.theta.ok = true ∧
    work2580.jac.invOK = true ∧ acceptsUnitSq work2580.out = true := by decide +kernel

def cell2580 : CellCertificate where
  tauBall := tau2580
  contactCenter := center2580
  contactBall := contact2580
  work := work2580
  center_sq := center_sq2580
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2580.1
  jac_ok := checks2580.2.1
  accepted := checks2580.2.2

def tau2581 : RatBall :=
  ⟨⟨-121/640, -45/128⟩, 3/1280⟩
def center2581 : GaussianRat :=
  ⟨-36780017/250000000, -243731207/1000000000⟩
def contact2581 : RatBall := localContactBall tau2581 center2581
def work2581 : RoundedTauEval :=
  evalTau precision tau2581 contact2581 logTwoBall

theorem center_sq2581 : (center2581.re : ℝ)^2 +
    (center2581.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2581]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2581 : work2581.theta.ok = true ∧
    work2581.jac.invOK = true ∧ acceptsUnitSq work2581.out = true := by decide +kernel

def cell2581 : CellCertificate where
  tauBall := tau2581
  contactCenter := center2581
  contactBall := contact2581
  work := work2581
  center_sq := center_sq2581
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2581.1
  jac_ok := checks2581.2.1
  accepted := checks2581.2.2

def tau2582 : RatBall :=
  ⟨⟨-117/640, -229/640⟩, 3/1280⟩
def center2582 : GaussianRat :=
  ⟨-143146729/1000000000, -249118251/1000000000⟩
def contact2582 : RatBall := localContactBall tau2582 center2582
def work2582 : RoundedTauEval :=
  evalTau precision tau2582 contact2582 logTwoBall

theorem center_sq2582 : (center2582.re : ℝ)^2 +
    (center2582.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2582]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2582 : work2582.theta.ok = true ∧
    work2582.jac.invOK = true ∧ acceptsUnitSq work2582.out = true := by decide +kernel

def cell2582 : CellCertificate where
  tauBall := tau2582
  contactCenter := center2582
  contactBall := contact2582
  work := work2582
  center_sq := center_sq2582
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2582.1
  jac_ok := checks2582.2.1
  accepted := checks2582.2.2

def tau2583 : RatBall :=
  ⟨⟨-113/640, -231/640⟩, 3/1280⟩
def center2583 : GaussianRat :=
  ⟨-138783923/1000000000, -252176463/1000000000⟩
def contact2583 : RatBall := localContactBall tau2583 center2583
def work2583 : RoundedTauEval :=
  evalTau precision tau2583 contact2583 logTwoBall

theorem center_sq2583 : (center2583.re : ℝ)^2 +
    (center2583.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2583]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2583 : work2583.theta.ok = true ∧
    work2583.jac.invOK = true ∧ acceptsUnitSq work2583.out = true := by decide +kernel

def cell2583 : CellCertificate where
  tauBall := tau2583
  contactCenter := center2583
  contactBall := contact2583
  work := work2583
  center_sq := center_sq2583
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2583.1
  jac_ok := checks2583.2.1
  accepted := checks2583.2.2

def cells : List CellCertificate := [cell2576, cell2577, cell2578, cell2579, cell2580, cell2581, cell2582, cell2583]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0322

end


