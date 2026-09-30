-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0339
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0339
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:37:08.963522+00:00
-- url     : https://prove2.me/theorems/b8dffe46-46fe-435c-85fb-ef4b7cf6d8de
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0339` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0339` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0339` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0339 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0339.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0339 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0339

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2712 : RatBall :=
  ⟨⟨-13/128, -237/640⟩, 3/1280⟩
def center2712 : GaussianRat :=
  ⟨-40758673/500000000, -133178453/500000000⟩
def contact2712 : RatBall := localContactBall tau2712 center2712
def work2712 : RoundedTauEval :=
  evalTau precision tau2712 contact2712 logTwoBall

theorem center_sq2712 : (center2712.re : ℝ)^2 +
    (center2712.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2712]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2712 : work2712.theta.ok = true ∧
    work2712.jac.invOK = true ∧ acceptsUnitSq work2712.out = true := by decide +kernel

def cell2712 : CellCertificate where
  tauBall := tau2712
  contactCenter := center2712
  contactBall := contact2712
  work := work2712
  center_sq := center_sq2712
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2712.1
  jac_ok := checks2712.2.1
  accepted := checks2712.2.2

def tau2713 : RatBall :=
  ⟨⟨-127/640, -223/640⟩, 3/1280⟩
def center2713 : GaussianRat :=
  ⟨-153725769/1000000000, -120168019/500000000⟩
def contact2713 : RatBall := localContactBall tau2713 center2713
def work2713 : RoundedTauEval :=
  evalTau precision tau2713 contact2713 logTwoBall

theorem center_sq2713 : (center2713.re : ℝ)^2 +
    (center2713.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2713]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2713 : work2713.theta.ok = true ∧
    work2713.jac.invOK = true ∧ acceptsUnitSq work2713.out = true := by decide +kernel

def cell2713 : CellCertificate where
  tauBall := tau2713
  contactCenter := center2713
  contactBall := contact2713
  work := work2713
  center_sq := center_sq2713
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2713.1
  jac_ok := checks2713.2.1
  accepted := checks2713.2.2

def tau2714 : RatBall :=
  ⟨⟨-25/128, -223/640⟩, 3/1280⟩
def center2714 : GaussianRat :=
  ⟨-151411581/1000000000, -120348091/500000000⟩
def contact2714 : RatBall := localContactBall tau2714 center2714
def work2714 : RoundedTauEval :=
  evalTau precision tau2714 contact2714 logTwoBall

theorem center_sq2714 : (center2714.re : ℝ)^2 +
    (center2714.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2714]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2714 : work2714.theta.ok = true ∧
    work2714.jac.invOK = true ∧ acceptsUnitSq work2714.out = true := by decide +kernel

def cell2714 : CellCertificate where
  tauBall := tau2714
  contactCenter := center2714
  contactBall := contact2714
  work := work2714
  center_sq := center_sq2714
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2714.1
  jac_ok := checks2714.2.1
  accepted := checks2714.2.2

def tau2715 : RatBall :=
  ⟨⟨-127/640, -221/640⟩, 3/1280⟩
def center2715 : GaussianRat :=
  ⟨-38341447/250000000, -29753309/125000000⟩
def contact2715 : RatBall := localContactBall tau2715 center2715
def work2715 : RoundedTauEval :=
  evalTau precision tau2715 contact2715 logTwoBall

theorem center_sq2715 : (center2715.re : ℝ)^2 +
    (center2715.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2715]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2715 : work2715.theta.ok = true ∧
    work2715.jac.invOK = true ∧ acceptsUnitSq work2715.out = true := by decide +kernel

def cell2715 : CellCertificate where
  tauBall := tau2715
  contactCenter := center2715
  contactBall := contact2715
  work := work2715
  center_sq := center_sq2715
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2715.1
  jac_ok := checks2715.2.1
  accepted := checks2715.2.2

def tau2716 : RatBall :=
  ⟨⟨-25/128, -221/640⟩, 3/1280⟩
def center2716 : GaussianRat :=
  ⟨-151056059/1000000000, -238381849/1000000000⟩
def contact2716 : RatBall := localContactBall tau2716 center2716
def work2716 : RoundedTauEval :=
  evalTau precision tau2716 contact2716 logTwoBall

theorem center_sq2716 : (center2716.re : ℝ)^2 +
    (center2716.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2716]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2716 : work2716.theta.ok = true ∧
    work2716.jac.invOK = true ∧ acceptsUnitSq work2716.out = true := by decide +kernel

def cell2716 : CellCertificate where
  tauBall := tau2716
  contactCenter := center2716
  contactBall := contact2716
  work := work2716
  center_sq := center_sq2716
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2716.1
  jac_ok := checks2716.2.1
  accepted := checks2716.2.2

def tau2717 : RatBall :=
  ⟨⟨-123/640, -223/640⟩, 3/1280⟩
def center2717 : GaussianRat :=
  ⟨-74546313/500000000, -120525907/500000000⟩
def contact2717 : RatBall := localContactBall tau2717 center2717
def work2717 : RoundedTauEval :=
  evalTau precision tau2717 contact2717 logTwoBall

theorem center_sq2717 : (center2717.re : ℝ)^2 +
    (center2717.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2717]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2717 : work2717.theta.ok = true ∧
    work2717.jac.invOK = true ∧ acceptsUnitSq work2717.out = true := by decide +kernel

def cell2717 : CellCertificate where
  tauBall := tau2717
  contactCenter := center2717
  contactBall := contact2717
  work := work2717
  center_sq := center_sq2717
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2717.1
  jac_ok := checks2717.2.1
  accepted := checks2717.2.2

def tau2718 : RatBall :=
  ⟨⟨-121/640, -223/640⟩, 3/1280⟩
def center2718 : GaussianRat :=
  ⟨-146768957/1000000000, -60350721/250000000⟩
def contact2718 : RatBall := localContactBall tau2718 center2718
def work2718 : RoundedTauEval :=
  evalTau precision tau2718 contact2718 logTwoBall

theorem center_sq2718 : (center2718.re : ℝ)^2 +
    (center2718.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2718]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2718 : work2718.theta.ok = true ∧
    work2718.jac.invOK = true ∧ acceptsUnitSq work2718.out = true := by decide +kernel

def cell2718 : CellCertificate where
  tauBall := tau2718
  contactCenter := center2718
  contactBall := contact2718
  work := work2718
  center_sq := center_sq2718
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2718.1
  jac_ok := checks2718.2.1
  accepted := checks2718.2.2

def tau2719 : RatBall :=
  ⟨⟨-123/640, -221/640⟩, 3/1280⟩
def center2719 : GaussianRat :=
  ⟨-29748323/200000000, -119366383/500000000⟩
def contact2719 : RatBall := localContactBall tau2719 center2719
def work2719 : RoundedTauEval :=
  evalTau precision tau2719 contact2719 logTwoBall

theorem center_sq2719 : (center2719.re : ℝ)^2 +
    (center2719.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2719]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2719 : work2719.theta.ok = true ∧
    work2719.jac.invOK = true ∧ acceptsUnitSq work2719.out = true := by decide +kernel

def cell2719 : CellCertificate where
  tauBall := tau2719
  contactCenter := center2719
  contactBall := contact2719
  work := work2719
  center_sq := center_sq2719
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2719.1
  jac_ok := checks2719.2.1
  accepted := checks2719.2.2

def cells : List CellCertificate := [cell2712, cell2713, cell2714, cell2715, cell2716, cell2717, cell2718, cell2719]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0339

end


