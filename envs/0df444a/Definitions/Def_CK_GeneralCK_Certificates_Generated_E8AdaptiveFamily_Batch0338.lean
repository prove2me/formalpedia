-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0338
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0338
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:53:05.466764+00:00
-- url     : https://prove2.me/theorems/f7f05978-345b-45a3-bb6d-6924bfb33470
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0338` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0338` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0338` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0338 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0338.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0338 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0338

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2704 : RatBall :=
  ⟨⟨-73/640, -237/640⟩, 3/1280⟩
def center2704 : GaussianRat :=
  ⟨-45695259/500000000, -6635463/25000000⟩
def contact2704 : RatBall := localContactBall tau2704 center2704
def work2704 : RoundedTauEval :=
  evalTau precision tau2704 contact2704 logTwoBall

theorem center_sq2704 : (center2704.re : ℝ)^2 +
    (center2704.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2704]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2704 : work2704.theta.ok = true ∧
    work2704.jac.invOK = true ∧ acceptsUnitSq work2704.out = true := by decide +kernel

def cell2704 : CellCertificate where
  tauBall := tau2704
  contactCenter := center2704
  contactBall := contact2704
  work := work2704
  center_sq := center_sq2704
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2704.1
  jac_ok := checks2704.2.1
  accepted := checks2704.2.2

def tau2705 : RatBall :=
  ⟨⟨-71/640, -239/640⟩, 3/1280⟩
def center2705 : GaussianRat :=
  ⟨-89169649/1000000000, -67032703/250000000⟩
def contact2705 : RatBall := localContactBall tau2705 center2705
def work2705 : RoundedTauEval :=
  evalTau precision tau2705 contact2705 logTwoBall

theorem center_sq2705 : (center2705.re : ℝ)^2 +
    (center2705.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2705]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2705 : work2705.theta.ok = true ∧
    work2705.jac.invOK = true ∧ acceptsUnitSq work2705.out = true := by decide +kernel

def cell2705 : CellCertificate where
  tauBall := tau2705
  contactCenter := center2705
  contactBall := contact2705
  work := work2705
  center_sq := center_sq2705
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2705.1
  jac_ok := checks2705.2.1
  accepted := checks2705.2.2

def tau2706 : RatBall :=
  ⟨⟨-69/640, -239/640⟩, 3/1280⟩
def center2706 : GaussianRat :=
  ⟨-43348293/500000000, -268371857/1000000000⟩
def contact2706 : RatBall := localContactBall tau2706 center2706
def work2706 : RoundedTauEval :=
  evalTau precision tau2706 contact2706 logTwoBall

theorem center_sq2706 : (center2706.re : ℝ)^2 +
    (center2706.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2706]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2706 : work2706.theta.ok = true ∧
    work2706.jac.invOK = true ∧ acceptsUnitSq work2706.out = true := by decide +kernel

def cell2706 : CellCertificate where
  tauBall := tau2706
  contactCenter := center2706
  contactBall := contact2706
  work := work2706
  center_sq := center_sq2706
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2706.1
  jac_ok := checks2706.2.1
  accepted := checks2706.2.2

def tau2707 : RatBall :=
  ⟨⟨-71/640, -237/640⟩, 3/1280⟩
def center2707 : GaussianRat :=
  ⟨-2223177/25000000, -53132513/200000000⟩
def contact2707 : RatBall := localContactBall tau2707 center2707
def work2707 : RoundedTauEval :=
  evalTau precision tau2707 contact2707 logTwoBall

theorem center_sq2707 : (center2707.re : ℝ)^2 +
    (center2707.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2707]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2707 : work2707.theta.ok = true ∧
    work2707.jac.invOK = true ∧ acceptsUnitSq work2707.out = true := by decide +kernel

def cell2707 : CellCertificate where
  tauBall := tau2707
  contactCenter := center2707
  contactBall := contact2707
  work := work2707
  center_sq := center_sq2707
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2707.1
  jac_ok := checks2707.2.1
  accepted := checks2707.2.2

def tau2708 : RatBall :=
  ⟨⟨-69/640, -237/640⟩, 3/1280⟩
def center2708 : GaussianRat :=
  ⟨-86460351/1000000000, -265900339/1000000000⟩
def contact2708 : RatBall := localContactBall tau2708 center2708
def work2708 : RoundedTauEval :=
  evalTau precision tau2708 contact2708 logTwoBall

theorem center_sq2708 : (center2708.re : ℝ)^2 +
    (center2708.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2708]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2708 : work2708.theta.ok = true ∧
    work2708.jac.invOK = true ∧ acceptsUnitSq work2708.out = true := by decide +kernel

def cell2708 : CellCertificate where
  tauBall := tau2708
  contactCenter := center2708
  contactBall := contact2708
  work := work2708
  center_sq := center_sq2708
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2708.1
  jac_ok := checks2708.2.1
  accepted := checks2708.2.2

def tau2709 : RatBall :=
  ⟨⟨-67/640, -239/640⟩, 3/1280⟩
def center2709 : GaussianRat :=
  ⟨-5263767/62500000, -134303253/500000000⟩
def contact2709 : RatBall := localContactBall tau2709 center2709
def work2709 : RoundedTauEval :=
  evalTau precision tau2709 contact2709 logTwoBall

theorem center_sq2709 : (center2709.re : ℝ)^2 +
    (center2709.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2709]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2709 : work2709.theta.ok = true ∧
    work2709.jac.invOK = true ∧ acceptsUnitSq work2709.out = true := by decide +kernel

def cell2709 : CellCertificate where
  tauBall := tau2709
  contactCenter := center2709
  contactBall := contact2709
  work := work2709
  center_sq := center_sq2709
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2709.1
  jac_ok := checks2709.2.1
  accepted := checks2709.2.2

def tau2710 : RatBall :=
  ⟨⟨-13/128, -239/640⟩, 3/1280⟩
def center2710 : GaussianRat :=
  ⟨-81740791/1000000000, -268834717/1000000000⟩
def contact2710 : RatBall := localContactBall tau2710 center2710
def work2710 : RoundedTauEval :=
  evalTau precision tau2710 contact2710 logTwoBall

theorem center_sq2710 : (center2710.re : ℝ)^2 +
    (center2710.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2710]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2710 : work2710.theta.ok = true ∧
    work2710.jac.invOK = true ∧ acceptsUnitSq work2710.out = true := by decide +kernel

def cell2710 : CellCertificate where
  tauBall := tau2710
  contactCenter := center2710
  contactBall := contact2710
  work := work2710
  center_sq := center_sq2710
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2710.1
  jac_ok := checks2710.2.1
  accepted := checks2710.2.2

def tau2711 : RatBall :=
  ⟨⟨-67/640, -237/640⟩, 3/1280⟩
def center2711 : GaussianRat :=
  ⟨-20997603/250000000, -266131799/1000000000⟩
def contact2711 : RatBall := localContactBall tau2711 center2711
def work2711 : RoundedTauEval :=
  evalTau precision tau2711 contact2711 logTwoBall

theorem center_sq2711 : (center2711.re : ℝ)^2 +
    (center2711.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2711]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2711 : work2711.theta.ok = true ∧
    work2711.jac.invOK = true ∧ acceptsUnitSq work2711.out = true := by decide +kernel

def cell2711 : CellCertificate where
  tauBall := tau2711
  contactCenter := center2711
  contactBall := contact2711
  work := work2711
  center_sq := center_sq2711
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2711.1
  jac_ok := checks2711.2.1
  accepted := checks2711.2.2

def cells : List CellCertificate := [cell2704, cell2705, cell2706, cell2707, cell2708, cell2709, cell2710, cell2711]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0338

end


