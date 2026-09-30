-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0381_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0381_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:55:27.259237+00:00
-- url     : https://prove2.me/theorems/89ec8626-fa12-49a7-ab34-1af82a25bb2a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0381 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3048 : RatBall :=
  ⟨⟨67/640, -247/640⟩, 3/1280⟩
def center3048 : GaussianRat :=
  ⟨42585897/500000000, -278570563/1000000000⟩
def contact3048 : RatBall := localContactBall tau3048 center3048
def work3048 : RoundedTauEval :=
  evalTau precision tau3048 contact3048 logTwoBall

theorem center_sq3048 : (center3048.re : ℝ)^2 +
    (center3048.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3048]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3048 : work3048.theta.ok = true ∧
    work3048.jac.invOK = true ∧ acceptsUnitSq work3048.out = true := by decide +kernel

def cell3048 : CellCertificate where
  tauBall := tau3048
  contactCenter := center3048
  contactBall := contact3048
  work := work3048
  center_sq := center_sq3048
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3048.1
  jac_ok := checks3048.2.1
  accepted := checks3048.2.2

def tau3049 : RatBall :=
  ⟨⟨13/128, -49/128⟩, 3/1280⟩
def center3049 : GaussianRat :=
  ⟨41214889/500000000, -1726921/6250000⟩
def contact3049 : RatBall := localContactBall tau3049 center3049
def work3049 : RoundedTauEval :=
  evalTau precision tau3049 contact3049 logTwoBall

theorem center_sq3049 : (center3049.re : ℝ)^2 +
    (center3049.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3049]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3049 : work3049.theta.ok = true ∧
    work3049.jac.invOK = true ∧ acceptsUnitSq work3049.out = true := by decide +kernel

def cell3049 : CellCertificate where
  tauBall := tau3049
  contactCenter := center3049
  contactBall := contact3049
  work := work3049
  center_sq := center_sq3049
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3049.1
  jac_ok := checks3049.2.1
  accepted := checks3049.2.2

def tau3050 : RatBall :=
  ⟨⟨67/640, -49/128⟩, 3/1280⟩
def center3050 : GaussianRat :=
  ⟨42464509/500000000, -34508699/125000000⟩
def contact3050 : RatBall := localContactBall tau3050 center3050
def work3050 : RoundedTauEval :=
  evalTau precision tau3050 contact3050 logTwoBall

theorem center_sq3050 : (center3050.re : ℝ)^2 +
    (center3050.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3050]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3050 : work3050.theta.ok = true ∧
    work3050.jac.invOK = true ∧ acceptsUnitSq work3050.out = true := by decide +kernel

def cell3050 : CellCertificate where
  tauBall := tau3050
  contactCenter := center3050
  contactBall := contact3050
  work := work3050
  center_sq := center_sq3050
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3050.1
  jac_ok := checks3050.2.1
  accepted := checks3050.2.2

def tau3051 : RatBall :=
  ⟨⟨69/640, -247/640⟩, 3/1280⟩
def center3051 : GaussianRat :=
  ⟨87674459/1000000000, -278322741/1000000000⟩
def contact3051 : RatBall := localContactBall tau3051 center3051
def work3051 : RoundedTauEval :=
  evalTau precision tau3051 contact3051 logTwoBall

theorem center_sq3051 : (center3051.re : ℝ)^2 +
    (center3051.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3051]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3051 : work3051.theta.ok = true ∧
    work3051.jac.invOK = true ∧ acceptsUnitSq work3051.out = true := by decide +kernel

def cell3051 : CellCertificate where
  tauBall := tau3051
  contactCenter := center3051
  contactBall := contact3051
  work := work3051
  center_sq := center_sq3051
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3051.1
  jac_ok := checks3051.2.1
  accepted := checks3051.2.2

def tau3052 : RatBall :=
  ⟨⟨71/640, -247/640⟩, 3/1280⟩
def center3052 : GaussianRat :=
  ⟨90173701/1000000000, -278068181/1000000000⟩
def contact3052 : RatBall := localContactBall tau3052 center3052
def work3052 : RoundedTauEval :=
  evalTau precision tau3052 contact3052 logTwoBall

theorem center_sq3052 : (center3052.re : ℝ)^2 +
    (center3052.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3052]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3052 : work3052.theta.ok = true ∧
    work3052.jac.invOK = true ∧ acceptsUnitSq work3052.out = true := by decide +kernel

def cell3052 : CellCertificate where
  tauBall := tau3052
  contactCenter := center3052
  contactBall := contact3052
  work := work3052
  center_sq := center_sq3052
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3052.1
  jac_ok := checks3052.2.1
  accepted := checks3052.2.2

def tau3053 : RatBall :=
  ⟨⟨69/640, -49/128⟩, 3/1280⟩
def center3053 : GaussianRat :=
  ⟨43712483/500000000, -34478141/125000000⟩
def contact3053 : RatBall := localContactBall tau3053 center3053
def work3053 : RoundedTauEval :=
  evalTau precision tau3053 contact3053 logTwoBall

theorem center_sq3053 : (center3053.re : ℝ)^2 +
    (center3053.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3053]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3053 : work3053.theta.ok = true ∧
    work3053.jac.invOK = true ∧ acceptsUnitSq work3053.out = true := by decide +kernel

def cell3053 : CellCertificate where
  tauBall := tau3053
  contactCenter := center3053
  contactBall := contact3053
  work := work3053
  center_sq := center_sq3053
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3053.1
  jac_ok := checks3053.2.1
  accepted := checks3053.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381


