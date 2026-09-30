-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0476_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0476_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:22:47.678945+00:00
-- url     : https://prove2.me/theorems/6de59f52-3b34-4132-861b-3eaf59c89a79
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0476 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3808 : RatBall :=
  ⟨⟨103/640, 47/128⟩, 3/1280⟩
def center3808 : GaussianRat :=
  ⟨31890163/250000000, 51727193/200000000⟩
def contact3808 : RatBall := localContactBall tau3808 center3808
def work3808 : RoundedTauEval :=
  evalTau precision tau3808 contact3808 logTwoBall

theorem center_sq3808 : (center3808.re : ℝ)^2 +
    (center3808.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3808]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3808 : work3808.theta.ok = true ∧
    work3808.jac.invOK = true ∧ acceptsUnitSq work3808.out = true := by decide +kernel

def cell3808 : CellCertificate where
  tauBall := tau3808
  contactCenter := center3808
  contactBall := contact3808
  work := work3808
  center_sq := center_sq3808
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3808.1
  jac_ok := checks3808.2.1
  accepted := checks3808.2.2

def tau3809 : RatBall :=
  ⟨⟨97/640, 237/640⟩, 3/1280⟩
def center3809 : GaussianRat :=
  ⟨60333117/500000000, 6550423/25000000⟩
def contact3809 : RatBall := localContactBall tau3809 center3809
def work3809 : RoundedTauEval :=
  evalTau precision tau3809 contact3809 logTwoBall

theorem center_sq3809 : (center3809.re : ℝ)^2 +
    (center3809.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3809]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3809 : work3809.theta.ok = true ∧
    work3809.jac.invOK = true ∧ acceptsUnitSq work3809.out = true := by decide +kernel

def cell3809 : CellCertificate where
  tauBall := tau3809
  contactCenter := center3809
  contactBall := contact3809
  work := work3809
  center_sq := center_sq3809
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3809.1
  jac_ok := checks3809.2.1
  accepted := checks3809.2.2

def tau3810 : RatBall :=
  ⟨⟨99/640, 237/640⟩, 3/1280⟩
def center3810 : GaussianRat :=
  ⟨123079793/1000000000, 65423867/250000000⟩
def contact3810 : RatBall := localContactBall tau3810 center3810
def work3810 : RoundedTauEval :=
  evalTau precision tau3810 contact3810 logTwoBall

theorem center_sq3810 : (center3810.re : ℝ)^2 +
    (center3810.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3810]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3810 : work3810.theta.ok = true ∧
    work3810.jac.invOK = true ∧ acceptsUnitSq work3810.out = true := by decide +kernel

def cell3810 : CellCertificate where
  tauBall := tau3810
  contactCenter := center3810
  contactBall := contact3810
  work := work3810
  center_sq := center_sq3810
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3810.1
  jac_ok := checks3810.2.1
  accepted := checks3810.2.2

def tau3811 : RatBall :=
  ⟨⟨21/128, 233/640⟩, 3/1280⟩
def center3811 : GaussianRat :=
  ⟨8101339/62500000, 3998631/15625000⟩
def contact3811 : RatBall := localContactBall tau3811 center3811
def work3811 : RoundedTauEval :=
  evalTau precision tau3811 contact3811 logTwoBall

theorem center_sq3811 : (center3811.re : ℝ)^2 +
    (center3811.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3811]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3811 : work3811.theta.ok = true ∧
    work3811.jac.invOK = true ∧ acceptsUnitSq work3811.out = true := by decide +kernel

def cell3811 : CellCertificate where
  tauBall := tau3811
  contactCenter := center3811
  contactBall := contact3811
  work := work3811
  center_sq := center_sq3811
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3811.1
  jac_ok := checks3811.2.1
  accepted := checks3811.2.2

def tau3812 : RatBall :=
  ⟨⟨107/640, 233/640⟩, 3/1280⟩
def center3812 : GaussianRat :=
  ⟨132006469/1000000000, 255577867/1000000000⟩
def contact3812 : RatBall := localContactBall tau3812 center3812
def work3812 : RoundedTauEval :=
  evalTau precision tau3812 contact3812 logTwoBall

theorem center_sq3812 : (center3812.re : ℝ)^2 +
    (center3812.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3812]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3812 : work3812.theta.ok = true ∧
    work3812.jac.invOK = true ∧ acceptsUnitSq work3812.out = true := by decide +kernel

def cell3812 : CellCertificate where
  tauBall := tau3812
  contactCenter := center3812
  contactBall := contact3812
  work := work3812
  center_sq := center_sq3812
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3812.1
  jac_ok := checks3812.2.1
  accepted := checks3812.2.2

def tau3813 : RatBall :=
  ⟨⟨109/640, 233/640⟩, 3/1280⟩
def center3813 : GaussianRat :=
  ⟨134387007/1000000000, 127619041/500000000⟩
def contact3813 : RatBall := localContactBall tau3813 center3813
def work3813 : RoundedTauEval :=
  evalTau precision tau3813 contact3813 logTwoBall

theorem center_sq3813 : (center3813.re : ℝ)^2 +
    (center3813.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3813]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3813 : work3813.theta.ok = true ∧
    work3813.jac.invOK = true ∧ acceptsUnitSq work3813.out = true := by decide +kernel

def cell3813 : CellCertificate where
  tauBall := tau3813
  contactCenter := center3813
  contactBall := contact3813
  work := work3813
  center_sq := center_sq3813
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3813.1
  jac_ok := checks3813.2.1
  accepted := checks3813.2.2

def tau3814 : RatBall :=
  ⟨⟨113/640, 45/128⟩, 3/1280⟩
def center3814 : GaussianRat :=
  ⟨137760383/1000000000, 245107147/1000000000⟩
def contact3814 : RatBall := localContactBall tau3814 center3814
def work3814 : RoundedTauEval :=
  evalTau precision tau3814 contact3814 logTwoBall

theorem center_sq3814 : (center3814.re : ℝ)^2 +
    (center3814.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3814]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476


