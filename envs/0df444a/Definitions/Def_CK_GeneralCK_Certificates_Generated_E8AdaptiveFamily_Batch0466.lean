-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0466
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0466
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:46:16.124223+00:00
-- url     : https://prove2.me/theorems/022a57e0-bee2-42aa-89c3-20aaa42f4964
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0466` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0466` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0466` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0466 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0466.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0466 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0466

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3728 : RatBall :=
  ⟨⟨87/640, 237/640⟩, 3/1280⟩
def center3728 : GaussianRat :=
  ⟨108535671/1000000000, 263538231/1000000000⟩
def contact3728 : RatBall := localContactBall tau3728 center3728
def work3728 : RoundedTauEval :=
  evalTau precision tau3728 contact3728 logTwoBall

theorem center_sq3728 : (center3728.re : ℝ)^2 +
    (center3728.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3728]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3728 : work3728.theta.ok = true ∧
    work3728.jac.invOK = true ∧ acceptsUnitSq work3728.out = true := by decide +kernel

def cell3728 : CellCertificate where
  tauBall := tau3728
  contactCenter := center3728
  contactBall := contact3728
  work := work3728
  center_sq := center_sq3728
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3728.1
  jac_ok := checks3728.2.1
  accepted := checks3728.2.2

def tau3729 : RatBall :=
  ⟨⟨17/128, 239/640⟩, 3/1280⟩
def center3729 : GaussianRat :=
  ⟨10638319/100000000, 266268043/1000000000⟩
def contact3729 : RatBall := localContactBall tau3729 center3729
def work3729 : RoundedTauEval :=
  evalTau precision tau3729 contact3729 logTwoBall

theorem center_sq3729 : (center3729.re : ℝ)^2 +
    (center3729.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3729]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3729 : work3729.theta.ok = true ∧
    work3729.jac.invOK = true ∧ acceptsUnitSq work3729.out = true := by decide +kernel

def cell3729 : CellCertificate where
  tauBall := tau3729
  contactCenter := center3729
  contactBall := contact3729
  work := work3729
  center_sq := center_sq3729
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3729.1
  jac_ok := checks3729.2.1
  accepted := checks3729.2.2

def tau3730 : RatBall :=
  ⟨⟨87/640, 239/640⟩, 3/1280⟩
def center3730 : GaussianRat :=
  ⟨4353093/40000000, 53195483/200000000⟩
def contact3730 : RatBall := localContactBall tau3730 center3730
def work3730 : RoundedTauEval :=
  evalTau precision tau3730 contact3730 logTwoBall

theorem center_sq3730 : (center3730.re : ℝ)^2 +
    (center3730.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3730]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3730 : work3730.theta.ok = true ∧
    work3730.jac.invOK = true ∧ acceptsUnitSq work3730.out = true := by decide +kernel

def cell3730 : CellCertificate where
  tauBall := tau3730
  contactCenter := center3730
  contactBall := contact3730
  work := work3730
  center_sq := center_sq3730
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3730.1
  jac_ok := checks3730.2.1
  accepted := checks3730.2.2

def tau3731 : RatBall :=
  ⟨⟨89/640, 233/640⟩, 3/1280⟩
def center3731 : GaussianRat :=
  ⟨22077337/200000000, 258392707/1000000000⟩
def contact3731 : RatBall := localContactBall tau3731 center3731
def work3731 : RoundedTauEval :=
  evalTau precision tau3731 contact3731 logTwoBall

theorem center_sq3731 : (center3731.re : ℝ)^2 +
    (center3731.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3731]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3731 : work3731.theta.ok = true ∧
    work3731.jac.invOK = true ∧ acceptsUnitSq work3731.out = true := by decide +kernel

def cell3731 : CellCertificate where
  tauBall := tau3731
  contactCenter := center3731
  contactBall := contact3731
  work := work3731
  center_sq := center_sq3731
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3731.1
  jac_ok := checks3731.2.1
  accepted := checks3731.2.2

def tau3732 : RatBall :=
  ⟨⟨91/640, 233/640⟩, 3/1280⟩
def center3732 : GaussianRat :=
  ⟨112805403/1000000000, 25810217/100000000⟩
def contact3732 : RatBall := localContactBall tau3732 center3732
def work3732 : RoundedTauEval :=
  evalTau precision tau3732 contact3732 logTwoBall

theorem center_sq3732 : (center3732.re : ℝ)^2 +
    (center3732.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3732]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3732 : work3732.theta.ok = true ∧
    work3732.jac.invOK = true ∧ acceptsUnitSq work3732.out = true := by decide +kernel

def cell3732 : CellCertificate where
  tauBall := tau3732
  contactCenter := center3732
  contactBall := contact3732
  work := work3732
  center_sq := center_sq3732
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3732.1
  jac_ok := checks3732.2.1
  accepted := checks3732.2.2

def tau3733 : RatBall :=
  ⟨⟨89/640, 47/128⟩, 3/1280⟩
def center3733 : GaussianRat :=
  ⟨110676327/1000000000, 2037627/7812500⟩
def contact3733 : RatBall := localContactBall tau3733 center3733
def work3733 : RoundedTauEval :=
  evalTau precision tau3733 contact3733 logTwoBall

theorem center_sq3733 : (center3733.re : ℝ)^2 +
    (center3733.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3733]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3733 : work3733.theta.ok = true ∧
    work3733.jac.invOK = true ∧ acceptsUnitSq work3733.out = true := by decide +kernel

def cell3733 : CellCertificate where
  tauBall := tau3733
  contactCenter := center3733
  contactBall := contact3733
  work := work3733
  center_sq := center_sq3733
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3733.1
  jac_ok := checks3733.2.1
  accepted := checks3733.2.2

def tau3734 : RatBall :=
  ⟨⟨91/640, 47/128⟩, 3/1280⟩
def center3734 : GaussianRat :=
  ⟨14137597/125000000, 260521763/1000000000⟩
def contact3734 : RatBall := localContactBall tau3734 center3734
def work3734 : RoundedTauEval :=
  evalTau precision tau3734 contact3734 logTwoBall

theorem center_sq3734 : (center3734.re : ℝ)^2 +
    (center3734.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3734]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3734 : work3734.theta.ok = true ∧
    work3734.jac.invOK = true ∧ acceptsUnitSq work3734.out = true := by decide +kernel

def cell3734 : CellCertificate where
  tauBall := tau3734
  contactCenter := center3734
  contactBall := contact3734
  work := work3734
  center_sq := center_sq3734
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3734.1
  jac_ok := checks3734.2.1
  accepted := checks3734.2.2

def tau3735 : RatBall :=
  ⟨⟨93/640, 233/640⟩, 3/1280⟩
def center3735 : GaussianRat :=
  ⟨115220153/1000000000, 257805963/1000000000⟩
def contact3735 : RatBall := localContactBall tau3735 center3735
def work3735 : RoundedTauEval :=
  evalTau precision tau3735 contact3735 logTwoBall

theorem center_sq3735 : (center3735.re : ℝ)^2 +
    (center3735.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3735]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3735 : work3735.theta.ok = true ∧
    work3735.jac.invOK = true ∧ acceptsUnitSq work3735.out = true := by decide +kernel

def cell3735 : CellCertificate where
  tauBall := tau3735
  contactCenter := center3735
  contactBall := contact3735
  work := work3735
  center_sq := center_sq3735
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3735.1
  jac_ok := checks3735.2.1
  accepted := checks3735.2.2

def cells : List CellCertificate := [cell3728, cell3729, cell3730, cell3731, cell3732, cell3733, cell3734, cell3735]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0466

end


