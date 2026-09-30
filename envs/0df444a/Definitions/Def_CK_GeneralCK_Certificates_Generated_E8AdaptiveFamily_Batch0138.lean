-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0138
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0138
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:47:52.275212+00:00
-- url     : https://prove2.me/theorems/550f6130-6a7c-48b4-b1ce-ae34cbcee6f5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0138` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0138` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0138` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0138 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0138.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0138 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0138

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1104 : RatBall :=
  ⟨⟨27/160, 9/32⟩, 3/320⟩
def center1104 : GaussianRat :=
  ⟨25128347/200000000, 9698989/50000000⟩
def contact1104 : RatBall := localContactBall tau1104 center1104
def work1104 : RoundedTauEval :=
  evalTau precision tau1104 contact1104 logTwoBall

theorem center_sq1104 : (center1104.re : ℝ)^2 +
    (center1104.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1104]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1104 : work1104.theta.ok = true ∧
    work1104.jac.invOK = true ∧ acceptsUnitSq work1104.out = true := by decide +kernel

def cell1104 : CellCertificate where
  tauBall := tau1104
  contactCenter := center1104
  contactBall := contact1104
  work := work1104
  center_sq := center_sq1104
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1104.1
  jac_ok := checks1104.2.1
  accepted := checks1104.2.2

def tau1105 : RatBall :=
  ⟨⟨5/32, 47/160⟩, 3/320⟩
def center1105 : GaussianRat :=
  ⟨58736127/500000000, 40804889/200000000⟩
def contact1105 : RatBall := localContactBall tau1105 center1105
def work1105 : RoundedTauEval :=
  evalTau precision tau1105 contact1105 logTwoBall

theorem center_sq1105 : (center1105.re : ℝ)^2 +
    (center1105.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1105]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1105 : work1105.theta.ok = true ∧
    work1105.jac.invOK = true ∧ acceptsUnitSq work1105.out = true := by decide +kernel

def cell1105 : CellCertificate where
  tauBall := tau1105
  contactCenter := center1105
  contactBall := contact1105
  work := work1105
  center_sq := center_sq1105
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1105.1
  jac_ok := checks1105.2.1
  accepted := checks1105.2.2

def tau1106 : RatBall :=
  ⟨⟨27/160, 47/160⟩, 3/320⟩
def center1106 : GaussianRat :=
  ⟨31652671/250000000, 101529593/500000000⟩
def contact1106 : RatBall := localContactBall tau1106 center1106
def work1106 : RoundedTauEval :=
  evalTau precision tau1106 contact1106 logTwoBall

theorem center_sq1106 : (center1106.re : ℝ)^2 +
    (center1106.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1106]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1106 : work1106.theta.ok = true ∧
    work1106.jac.invOK = true ∧ acceptsUnitSq work1106.out = true := by decide +kernel

def cell1106 : CellCertificate where
  tauBall := tau1106
  contactCenter := center1106
  contactBall := contact1106
  work := work1106
  center_sq := center_sq1106
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1106.1
  jac_ok := checks1106.2.1
  accepted := checks1106.2.2

def tau1107 : RatBall :=
  ⟨⟨29/160, 9/32⟩, 3/320⟩
def center1107 : GaussianRat :=
  ⟨67331309/500000000, 193009163/1000000000⟩
def contact1107 : RatBall := localContactBall tau1107 center1107
def work1107 : RoundedTauEval :=
  evalTau precision tau1107 contact1107 logTwoBall

theorem center_sq1107 : (center1107.re : ℝ)^2 +
    (center1107.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1107]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1107 : work1107.theta.ok = true ∧
    work1107.jac.invOK = true ∧ acceptsUnitSq work1107.out = true := by decide +kernel

def cell1107 : CellCertificate where
  tauBall := tau1107
  contactCenter := center1107
  contactBall := contact1107
  work := work1107
  center_sq := center_sq1107
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1107.1
  jac_ok := checks1107.2.1
  accepted := checks1107.2.2

def tau1108 : RatBall :=
  ⟨⟨31/160, 9/32⟩, 3/320⟩
def center1108 : GaussianRat :=
  ⟨143625227/1000000000, 38396169/200000000⟩
def contact1108 : RatBall := localContactBall tau1108 center1108
def work1108 : RoundedTauEval :=
  evalTau precision tau1108 contact1108 logTwoBall

theorem center_sq1108 : (center1108.re : ℝ)^2 +
    (center1108.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1108]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1108 : work1108.theta.ok = true ∧
    work1108.jac.invOK = true ∧ acceptsUnitSq work1108.out = true := by decide +kernel

def cell1108 : CellCertificate where
  tauBall := tau1108
  contactCenter := center1108
  contactBall := contact1108
  work := work1108
  center_sq := center_sq1108
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1108.1
  jac_ok := checks1108.2.1
  accepted := checks1108.2.2

def tau1109 : RatBall :=
  ⟨⟨29/160, 47/160⟩, 3/320⟩
def center1109 : GaussianRat :=
  ⟨135691941/1000000000, 202030811/1000000000⟩
def contact1109 : RatBall := localContactBall tau1109 center1109
def work1109 : RoundedTauEval :=
  evalTau precision tau1109 contact1109 logTwoBall

theorem center_sq1109 : (center1109.re : ℝ)^2 +
    (center1109.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1109]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1109 : work1109.theta.ok = true ∧
    work1109.jac.invOK = true ∧ acceptsUnitSq work1109.out = true := by decide +kernel

def cell1109 : CellCertificate where
  tauBall := tau1109
  contactCenter := center1109
  contactBall := contact1109
  work := work1109
  center_sq := center_sq1109
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1109.1
  jac_ok := checks1109.2.1
  accepted := checks1109.2.2

def tau1110 : RatBall :=
  ⟨⟨31/160, 47/160⟩, 3/320⟩
def center1110 : GaussianRat :=
  ⟨5788509/40000000, 200941561/1000000000⟩
def contact1110 : RatBall := localContactBall tau1110 center1110
def work1110 : RoundedTauEval :=
  evalTau precision tau1110 contact1110 logTwoBall

theorem center_sq1110 : (center1110.re : ℝ)^2 +
    (center1110.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1110]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1110 : work1110.theta.ok = true ∧
    work1110.jac.invOK = true ∧ acceptsUnitSq work1110.out = true := by decide +kernel

def cell1110 : CellCertificate where
  tauBall := tau1110
  contactCenter := center1110
  contactBall := contact1110
  work := work1110
  center_sq := center_sq1110
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1110.1
  jac_ok := checks1110.2.1
  accepted := checks1110.2.2

def tau1111 : RatBall :=
  ⟨⟨1/160, 49/160⟩, 3/320⟩
def center1111 : GaussianRat :=
  ⟨1199829/250000000, 109796019/500000000⟩
def contact1111 : RatBall := localContactBall tau1111 center1111
def work1111 : RoundedTauEval :=
  evalTau precision tau1111 contact1111 logTwoBall

theorem center_sq1111 : (center1111.re : ℝ)^2 +
    (center1111.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1111]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1111 : work1111.theta.ok = true ∧
    work1111.jac.invOK = true ∧ acceptsUnitSq work1111.out = true := by decide +kernel

def cell1111 : CellCertificate where
  tauBall := tau1111
  contactCenter := center1111
  contactBall := contact1111
  work := work1111
  center_sq := center_sq1111
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1111.1
  jac_ok := checks1111.2.1
  accepted := checks1111.2.2

def cells : List CellCertificate := [cell1104, cell1105, cell1106, cell1107, cell1108, cell1109, cell1110, cell1111]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0138

end


