-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0450_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0450_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:03:49.826669+00:00
-- url     : https://prove2.me/theorems/1bc7fef9-2e76-42a5-bbab-9517a8253f17
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0450 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0450 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0450 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0450 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0450 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0450

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3600 : RatBall :=
  ⟨⟨33/640, 49/128⟩, 3/1280⟩
def center3600 : GaussianRat :=
  ⟨42068541/1000000000, 27916967/100000000⟩
def contact3600 : RatBall := localContactBall tau3600 center3600
def work3600 : RoundedTauEval :=
  evalTau precision tau3600 contact3600 logTwoBall

theorem center_sq3600 : (center3600.re : ℝ)^2 +
    (center3600.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3600]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3600 : work3600.theta.ok = true ∧
    work3600.jac.invOK = true ∧ acceptsUnitSq work3600.out = true := by decide +kernel

def cell3600 : CellCertificate where
  tauBall := tau3600
  contactCenter := center3600
  contactBall := contact3600
  work := work3600
  center_sq := center_sq3600
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3600.1
  jac_ok := checks3600.2.1
  accepted := checks3600.2.2

def tau3601 : RatBall :=
  ⟨⟨7/128, 49/128⟩, 3/1280⟩
def center3601 : GaussianRat :=
  ⟨44607937/1000000000, 279044067/1000000000⟩
def contact3601 : RatBall := localContactBall tau3601 center3601
def work3601 : RoundedTauEval :=
  evalTau precision tau3601 contact3601 logTwoBall

theorem center_sq3601 : (center3601.re : ℝ)^2 +
    (center3601.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3601]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3601 : work3601.theta.ok = true ∧
    work3601.jac.invOK = true ∧ acceptsUnitSq work3601.out = true := by decide +kernel

def cell3601 : CellCertificate where
  tauBall := tau3601
  contactCenter := center3601
  contactBall := contact3601
  work := work3601
  center_sq := center_sq3601
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3601.1
  jac_ok := checks3601.2.1
  accepted := checks3601.2.2

def tau3602 : RatBall :=
  ⟨⟨33/640, 247/640⟩, 3/1280⟩
def center3602 : GaussianRat :=
  ⟨8438273/200000000, 281713577/1000000000⟩
def contact3602 : RatBall := localContactBall tau3602 center3602
def work3602 : RoundedTauEval :=
  evalTau precision tau3602 contact3602 logTwoBall

theorem center_sq3602 : (center3602.re : ℝ)^2 +
    (center3602.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3602]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3602 : work3602.theta.ok = true ∧
    work3602.jac.invOK = true ∧ acceptsUnitSq work3602.out = true := by decide +kernel

def cell3602 : CellCertificate where
  tauBall := tau3602
  contactCenter := center3602
  contactBall := contact3602
  work := work3602
  center_sq := center_sq3602
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3602.1
  jac_ok := checks3602.2.1
  accepted := checks3602.2.2

def tau3603 : RatBall :=
  ⟨⟨7/128, 247/640⟩, 3/1280⟩
def center3603 : GaussianRat :=
  ⟨2796129/62500000, 281586221/1000000000⟩
def contact3603 : RatBall := localContactBall tau3603 center3603
def work3603 : RoundedTauEval :=
  evalTau precision tau3603 contact3603 logTwoBall

theorem center_sq3603 : (center3603.re : ℝ)^2 +
    (center3603.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3603]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3603 : work3603.theta.ok = true ∧
    work3603.jac.invOK = true ∧ acceptsUnitSq work3603.out = true := by decide +kernel

def cell3603 : CellCertificate where
  tauBall := tau3603
  contactCenter := center3603
  contactBall := contact3603
  work := work3603
  center_sq := center_sq3603
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3603.1
  jac_ok := checks3603.2.1
  accepted := checks3603.2.2

def tau3604 : RatBall :=
  ⟨⟨37/640, 49/128⟩, 3/1280⟩
def center3604 : GaussianRat :=
  ⟨23572771/500000000, 278911223/1000000000⟩
def contact3604 : RatBall := localContactBall tau3604 center3604
def work3604 : RoundedTauEval :=
  evalTau precision tau3604 contact3604 logTwoBall

theorem center_sq3604 : (center3604.re : ℝ)^2 +
    (center3604.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3604]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3604 : work3604.theta.ok = true ∧
    work3604.jac.invOK = true ∧ acceptsUnitSq work3604.out = true := by decide +kernel

def cell3604 : CellCertificate where
  tauBall := tau3604
  contactCenter := center3604
  contactBall := contact3604
  work := work3604
  center_sq := center_sq3604
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3604.1
  jac_ok := checks3604.2.1
  accepted := checks3604.2.2

def tau3605 : RatBall :=
  ⟨⟨39/640, 49/128⟩, 3/1280⟩
def center3605 : GaussianRat :=
  ⟨49681259/1000000000, 139385581/500000000⟩
def contact3605 : RatBall := localContactBall tau3605 center3605
def work3605 : RoundedTauEval :=
  evalTau precision tau3605 contact3605 logTwoBall

theorem center_sq3605 : (center3605.re : ℝ)^2 +
    (center3605.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3605]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3605 : work3605.theta.ok = true ∧
    work3605.jac.invOK = true ∧ acceptsUnitSq work3605.out = true := by decide +kernel

def cell3605 : CellCertificate where
  tauBall := tau3605
  contactCenter := center3605
  contactBall := contact3605
  work := work3605
  center_sq := center_sq3605
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3605.1
  jac_ok := checks3605.2.1
  accepted := checks3605.2.2

def tau3606 : RatBall :=
  ⟨⟨37/640, 247/640⟩, 3/1280⟩
def center3606 : GaussianRat :=
  ⟨11820737/250000000, 11258061/40000000⟩
def contact3606 : RatBall := localContactBall tau3606 center3606

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0450


