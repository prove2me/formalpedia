-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0332
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0332
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:21:49.282784+00:00
-- url     : https://prove2.me/theorems/180b59b9-e0ef-4baa-b1b4-d65ae8b61169
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0332` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0332` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0332` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0332 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0332.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0332 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0332

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2656 : RatBall :=
  ⟨⟨-69/640, -241/640⟩, 3/1280⟩
def center2656 : GaussianRat :=
  ⟨-10867009/125000000, -67712443/250000000⟩
def contact2656 : RatBall := localContactBall tau2656 center2656
def work2656 : RoundedTauEval :=
  evalTau precision tau2656 contact2656 logTwoBall

theorem center_sq2656 : (center2656.re : ℝ)^2 +
    (center2656.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2656]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2656 : work2656.theta.ok = true ∧
    work2656.jac.invOK = true ∧ acceptsUnitSq work2656.out = true := by decide +kernel

def cell2656 : CellCertificate where
  tauBall := tau2656
  contactCenter := center2656
  contactBall := contact2656
  work := work2656
  center_sq := center_sq2656
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2656.1
  jac_ok := checks2656.2.1
  accepted := checks2656.2.2

def tau2657 : RatBall :=
  ⟨⟨-67/640, -243/640⟩, 3/1280⟩
def center2657 : GaussianRat :=
  ⟨-42344767/500000000, -273575317/1000000000⟩
def contact2657 : RatBall := localContactBall tau2657 center2657
def work2657 : RoundedTauEval :=
  evalTau precision tau2657 contact2657 logTwoBall

theorem center_sq2657 : (center2657.re : ℝ)^2 +
    (center2657.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2657]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2657 : work2657.theta.ok = true ∧
    work2657.jac.invOK = true ∧ acceptsUnitSq work2657.out = true := by decide +kernel

def cell2657 : CellCertificate where
  tauBall := tau2657
  contactCenter := center2657
  contactBall := contact2657
  work := work2657
  center_sq := center_sq2657
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2657.1
  jac_ok := checks2657.2.1
  accepted := checks2657.2.2

def tau2658 : RatBall :=
  ⟨⟨-13/128, -243/640⟩, 3/1280⟩
def center2658 : GaussianRat :=
  ⟨-82196967/1000000000, -136904929/500000000⟩
def contact2658 : RatBall := localContactBall tau2658 center2658
def work2658 : RoundedTauEval :=
  evalTau precision tau2658 contact2658 logTwoBall

theorem center_sq2658 : (center2658.re : ℝ)^2 +
    (center2658.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2658]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2658 : work2658.theta.ok = true ∧
    work2658.jac.invOK = true ∧ acceptsUnitSq work2658.out = true := by decide +kernel

def cell2658 : CellCertificate where
  tauBall := tau2658
  contactCenter := center2658
  contactBall := contact2658
  work := work2658
  center_sq := center_sq2658
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2658.1
  jac_ok := checks2658.2.1
  accepted := checks2658.2.2

def tau2659 : RatBall :=
  ⟨⟨-67/640, -241/640⟩, 3/1280⟩
def center2659 : GaussianRat :=
  ⟨-84453299/1000000000, -5421753/20000000⟩
def contact2659 : RatBall := localContactBall tau2659 center2659
def work2659 : RoundedTauEval :=
  evalTau precision tau2659 contact2659 logTwoBall

theorem center_sq2659 : (center2659.re : ℝ)^2 +
    (center2659.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2659]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2659 : work2659.theta.ok = true ∧
    work2659.jac.invOK = true ∧ acceptsUnitSq work2659.out = true := by decide +kernel

def cell2659 : CellCertificate where
  tauBall := tau2659
  contactCenter := center2659
  contactBall := contact2659
  work := work2659
  center_sq := center_sq2659
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2659.1
  jac_ok := checks2659.2.1
  accepted := checks2659.2.2

def tau2660 : RatBall :=
  ⟨⟨-13/128, -241/640⟩, 3/1280⟩
def center2660 : GaussianRat :=
  ⟨-40983659/500000000, -135659503/500000000⟩
def contact2660 : RatBall := localContactBall tau2660 center2660
def work2660 : RoundedTauEval :=
  evalTau precision tau2660 contact2660 logTwoBall

theorem center_sq2660 : (center2660.re : ℝ)^2 +
    (center2660.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2660]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2660 : work2660.theta.ok = true ∧
    work2660.jac.invOK = true ∧ acceptsUnitSq work2660.out = true := by decide +kernel

def cell2660 : CellCertificate where
  tauBall := tau2660
  contactCenter := center2660
  contactBall := contact2660
  work := work2660
  center_sq := center_sq2660
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2660.1
  jac_ok := checks2660.2.1
  accepted := checks2660.2.2

def tau2661 : RatBall :=
  ⟨⟨-19/128, -239/640⟩, 3/1280⟩
def center2661 : GaussianRat :=
  ⟨-118563451/1000000000, -66188883/250000000⟩
def contact2661 : RatBall := localContactBall tau2661 center2661
def work2661 : RoundedTauEval :=
  evalTau precision tau2661 contact2661 logTwoBall

theorem center_sq2661 : (center2661.re : ℝ)^2 +
    (center2661.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2661]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2661 : work2661.theta.ok = true ∧
    work2661.jac.invOK = true ∧ acceptsUnitSq work2661.out = true := by decide +kernel

def cell2661 : CellCertificate where
  tauBall := tau2661
  contactCenter := center2661
  contactBall := contact2661
  work := work2661
  center_sq := center_sq2661
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2661.1
  jac_ok := checks2661.2.1
  accepted := checks2661.2.2

def tau2662 : RatBall :=
  ⟨⟨-93/640, -239/640⟩, 3/1280⟩
def center2662 : GaussianRat :=
  ⟨-116135629/1000000000, -265069807/1000000000⟩
def contact2662 : RatBall := localContactBall tau2662 center2662
def work2662 : RoundedTauEval :=
  evalTau precision tau2662 contact2662 logTwoBall

theorem center_sq2662 : (center2662.re : ℝ)^2 +
    (center2662.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2662]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2662 : work2662.theta.ok = true ∧
    work2662.jac.invOK = true ∧ acceptsUnitSq work2662.out = true := by decide +kernel

def cell2662 : CellCertificate where
  tauBall := tau2662
  contactCenter := center2662
  contactBall := contact2662
  work := work2662
  center_sq := center_sq2662
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2662.1
  jac_ok := checks2662.2.1
  accepted := checks2662.2.2

def tau2663 : RatBall :=
  ⟨⟨-19/128, -237/640⟩, 3/1280⟩
def center2663 : GaussianRat :=
  ⟨-29562099/250000000, -262332709/1000000000⟩
def contact2663 : RatBall := localContactBall tau2663 center2663
def work2663 : RoundedTauEval :=
  evalTau precision tau2663 contact2663 logTwoBall

theorem center_sq2663 : (center2663.re : ℝ)^2 +
    (center2663.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2663]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2663 : work2663.theta.ok = true ∧
    work2663.jac.invOK = true ∧ acceptsUnitSq work2663.out = true := by decide +kernel

def cell2663 : CellCertificate where
  tauBall := tau2663
  contactCenter := center2663
  contactBall := contact2663
  work := work2663
  center_sq := center_sq2663
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2663.1
  jac_ok := checks2663.2.1
  accepted := checks2663.2.2

def cells : List CellCertificate := [cell2656, cell2657, cell2658, cell2659, cell2660, cell2661, cell2662, cell2663]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0332

end


