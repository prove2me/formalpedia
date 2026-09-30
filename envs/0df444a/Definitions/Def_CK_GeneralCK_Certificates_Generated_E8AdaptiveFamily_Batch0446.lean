-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0446
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0446
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:46:08.972512+00:00
-- url     : https://prove2.me/theorems/52d72d7a-a6eb-42c4-8014-5d9044268b90
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0446` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0446` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0446` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0446 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0446.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0446 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0446

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3568 : RatBall :=
  ⟨⟨17/640, 249/640⟩, 3/1280⟩
def center3568 : GaussianRat :=
  ⟨10914601/500000000, 285027327/1000000000⟩
def contact3568 : RatBall := localContactBall tau3568 center3568
def work3568 : RoundedTauEval :=
  evalTau precision tau3568 contact3568 logTwoBall

theorem center_sq3568 : (center3568.re : ℝ)^2 +
    (center3568.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3568]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3568 : work3568.theta.ok = true ∧
    work3568.jac.invOK = true ∧ acceptsUnitSq work3568.out = true := by decide +kernel

def cell3568 : CellCertificate where
  tauBall := tau3568
  contactCenter := center3568
  contactBall := contact3568
  work := work3568
  center_sq := center_sq3568
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3568.1
  jac_ok := checks3568.2.1
  accepted := checks3568.2.2

def tau3569 : RatBall :=
  ⟨⟨19/640, 249/640⟩, 3/1280⟩
def center3569 : GaussianRat :=
  ⟨6098577/250000000, 142479251/500000000⟩
def contact3569 : RatBall := localContactBall tau3569 center3569
def work3569 : RoundedTauEval :=
  evalTau precision tau3569 contact3569 logTwoBall

theorem center_sq3569 : (center3569.re : ℝ)^2 +
    (center3569.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3569]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3569 : work3569.theta.ok = true ∧
    work3569.jac.invOK = true ∧ acceptsUnitSq work3569.out = true := by decide +kernel

def cell3569 : CellCertificate where
  tauBall := tau3569
  contactCenter := center3569
  contactBall := contact3569
  work := work3569
  center_sq := center_sq3569
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3569.1
  jac_ok := checks3569.2.1
  accepted := checks3569.2.2

def tau3570 : RatBall :=
  ⟨⟨17/640, 251/640⟩, 3/1280⟩
def center3570 : GaussianRat :=
  ⟨21894677/1000000000, 143798363/500000000⟩
def contact3570 : RatBall := localContactBall tau3570 center3570
def work3570 : RoundedTauEval :=
  evalTau precision tau3570 contact3570 logTwoBall

theorem center_sq3570 : (center3570.re : ℝ)^2 +
    (center3570.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3570]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3570 : work3570.theta.ok = true ∧
    work3570.jac.invOK = true ∧ acceptsUnitSq work3570.out = true := by decide +kernel

def cell3570 : CellCertificate where
  tauBall := tau3570
  contactCenter := center3570
  contactBall := contact3570
  work := work3570
  center_sq := center_sq3570
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3570.1
  jac_ok := checks3570.2.1
  accepted := checks3570.2.2

def tau3571 : RatBall :=
  ⟨⟨19/640, 251/640⟩, 3/1280⟩
def center3571 : GaussianRat :=
  ⟨12233721/500000000, 287526937/1000000000⟩
def contact3571 : RatBall := localContactBall tau3571 center3571
def work3571 : RoundedTauEval :=
  evalTau precision tau3571 contact3571 logTwoBall

theorem center_sq3571 : (center3571.re : ℝ)^2 +
    (center3571.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3571]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3571 : work3571.theta.ok = true ∧
    work3571.jac.invOK = true ∧ acceptsUnitSq work3571.out = true := by decide +kernel

def cell3571 : CellCertificate where
  tauBall := tau3571
  contactCenter := center3571
  contactBall := contact3571
  work := work3571
  center_sq := center_sq3571
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3571.1
  jac_ok := checks3571.2.1
  accepted := checks3571.2.2

def tau3572 : RatBall :=
  ⟨⟨21/640, 249/640⟩, 3/1280⟩
def center3572 : GaussianRat :=
  ⟨26958403/1000000000, 284882077/1000000000⟩
def contact3572 : RatBall := localContactBall tau3572 center3572
def work3572 : RoundedTauEval :=
  evalTau precision tau3572 contact3572 logTwoBall

theorem center_sq3572 : (center3572.re : ℝ)^2 +
    (center3572.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3572]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3572 : work3572.theta.ok = true ∧
    work3572.jac.invOK = true ∧ acceptsUnitSq work3572.out = true := by decide +kernel

def cell3572 : CellCertificate where
  tauBall := tau3572
  contactCenter := center3572
  contactBall := contact3572
  work := work3572
  center_sq := center_sq3572
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3572.1
  jac_ok := checks3572.2.1
  accepted := checks3572.2.2

def tau3573 : RatBall :=
  ⟨⟨23/640, 249/640⟩, 3/1280⟩
def center3573 : GaussianRat :=
  ⟨29521383/1000000000, 142399033/500000000⟩
def contact3573 : RatBall := localContactBall tau3573 center3573
def work3573 : RoundedTauEval :=
  evalTau precision tau3573 contact3573 logTwoBall

theorem center_sq3573 : (center3573.re : ℝ)^2 +
    (center3573.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3573]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3573 : work3573.theta.ok = true ∧
    work3573.jac.invOK = true ∧ acceptsUnitSq work3573.out = true := by decide +kernel

def cell3573 : CellCertificate where
  tauBall := tau3573
  contactCenter := center3573
  contactBall := contact3573
  work := work3573
  center_sq := center_sq3573
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3573.1
  jac_ok := checks3573.2.1
  accepted := checks3573.2.2

def tau3574 : RatBall :=
  ⟨⟨21/640, 251/640⟩, 3/1280⟩
def center3574 : GaussianRat :=
  ⟨1689949/62500000, 143724721/500000000⟩
def contact3574 : RatBall := localContactBall tau3574 center3574
def work3574 : RoundedTauEval :=
  evalTau precision tau3574 contact3574 logTwoBall

theorem center_sq3574 : (center3574.re : ℝ)^2 +
    (center3574.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3574]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3574 : work3574.theta.ok = true ∧
    work3574.jac.invOK = true ∧ acceptsUnitSq work3574.out = true := by decide +kernel

def cell3574 : CellCertificate where
  tauBall := tau3574
  contactCenter := center3574
  contactBall := contact3574
  work := work3574
  center_sq := center_sq3574
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3574.1
  jac_ok := checks3574.2.1
  accepted := checks3574.2.2

def tau3575 : RatBall :=
  ⟨⟨23/640, 251/640⟩, 3/1280⟩
def center3575 : GaussianRat :=
  ⟨14804897/500000000, 8980133/31250000⟩
def contact3575 : RatBall := localContactBall tau3575 center3575
def work3575 : RoundedTauEval :=
  evalTau precision tau3575 contact3575 logTwoBall

theorem center_sq3575 : (center3575.re : ℝ)^2 +
    (center3575.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3575]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3575 : work3575.theta.ok = true ∧
    work3575.jac.invOK = true ∧ acceptsUnitSq work3575.out = true := by decide +kernel

def cell3575 : CellCertificate where
  tauBall := tau3575
  contactCenter := center3575
  contactBall := contact3575
  work := work3575
  center_sq := center_sq3575
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3575.1
  jac_ok := checks3575.2.1
  accepted := checks3575.2.2

def cells : List CellCertificate := [cell3568, cell3569, cell3570, cell3571, cell3572, cell3573, cell3574, cell3575]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0446

end


