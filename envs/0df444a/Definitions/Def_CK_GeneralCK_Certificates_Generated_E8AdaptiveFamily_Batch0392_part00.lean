-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0392_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0392_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:49:37.71284+00:00
-- url     : https://prove2.me/theorems/b34bceb7-2847-40ff-b8c2-cebeab056970
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0392 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0392 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0392 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0392 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0392 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0392

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3136 : RatBall :=
  ⟨⟨99/640, -47/128⟩, 3/1280⟩
def center3136 : GaussianRat :=
  ⟨61378847/500000000, -129643433/500000000⟩
def contact3136 : RatBall := localContactBall tau3136 center3136
def work3136 : RoundedTauEval :=
  evalTau precision tau3136 contact3136 logTwoBall

theorem center_sq3136 : (center3136.re : ℝ)^2 +
    (center3136.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3136]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3136 : work3136.theta.ok = true ∧
    work3136.jac.invOK = true ∧ acceptsUnitSq work3136.out = true := by decide +kernel

def cell3136 : CellCertificate where
  tauBall := tau3136
  contactCenter := center3136
  contactBall := contact3136
  work := work3136
  center_sq := center_sq3136
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3136.1
  jac_ok := checks3136.2.1
  accepted := checks3136.2.2

def tau3137 : RatBall :=
  ⟨⟨97/640, -233/640⟩, 3/1280⟩
def center3137 : GaussianRat :=
  ⟨60018733/500000000, -257196731/1000000000⟩
def contact3137 : RatBall := localContactBall tau3137 center3137
def work3137 : RoundedTauEval :=
  evalTau precision tau3137 contact3137 logTwoBall

theorem center_sq3137 : (center3137.re : ℝ)^2 +
    (center3137.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3137]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3137 : work3137.theta.ok = true ∧
    work3137.jac.invOK = true ∧ acceptsUnitSq work3137.out = true := by decide +kernel

def cell3137 : CellCertificate where
  tauBall := tau3137
  contactCenter := center3137
  contactBall := contact3137
  work := work3137
  center_sq := center_sq3137
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3137.1
  jac_ok := checks3137.2.1
  accepted := checks3137.2.2

def tau3138 : RatBall :=
  ⟨⟨99/640, -233/640⟩, 3/1280⟩
def center3138 : GaussianRat :=
  ⟨122439891/1000000000, -51376761/200000000⟩
def contact3138 : RatBall := localContactBall tau3138 center3138
def work3138 : RoundedTauEval :=
  evalTau precision tau3138 contact3138 logTwoBall

theorem center_sq3138 : (center3138.re : ℝ)^2 +
    (center3138.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3138]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3138 : work3138.theta.ok = true ∧
    work3138.jac.invOK = true ∧ acceptsUnitSq work3138.out = true := by decide +kernel

def cell3138 : CellCertificate where
  tauBall := tau3138
  contactCenter := center3138
  contactBall := contact3138
  work := work3138
  center_sq := center_sq3138
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3138.1
  jac_ok := checks3138.2.1
  accepted := checks3138.2.2

def tau3139 : RatBall :=
  ⟨⟨101/640, -47/128⟩, 3/1280⟩
def center3139 : GaussianRat :=
  ⟨25032271/200000000, -809263/3125000⟩
def contact3139 : RatBall := localContactBall tau3139 center3139
def work3139 : RoundedTauEval :=
  evalTau precision tau3139 contact3139 logTwoBall

theorem center_sq3139 : (center3139.re : ℝ)^2 +
    (center3139.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3139]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3139 : work3139.theta.ok = true ∧
    work3139.jac.invOK = true ∧ acceptsUnitSq work3139.out = true := by decide +kernel

def cell3139 : CellCertificate where
  tauBall := tau3139
  contactCenter := center3139
  contactBall := contact3139
  work := work3139
  center_sq := center_sq3139
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3139.1
  jac_ok := checks3139.2.1
  accepted := checks3139.2.2

def tau3140 : RatBall :=
  ⟨⟨103/640, -47/128⟩, 3/1280⟩
def center3140 : GaussianRat :=
  ⟨31890163/250000000, -51727193/200000000⟩
def contact3140 : RatBall := localContactBall tau3140 center3140
def work3140 : RoundedTauEval :=
  evalTau precision tau3140 contact3140 logTwoBall

theorem center_sq3140 : (center3140.re : ℝ)^2 +
    (center3140.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3140]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3140 : work3140.theta.ok = true ∧
    work3140.jac.invOK = true ∧ acceptsUnitSq work3140.out = true := by decide +kernel

def cell3140 : CellCertificate where
  tauBall := tau3140
  contactCenter := center3140
  contactBall := contact3140
  work := work3140
  center_sq := center_sq3140
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3140.1
  jac_ok := checks3140.2.1
  accepted := checks3140.2.2

def tau3141 : RatBall :=
  ⟨⟨101/640, -233/640⟩, 3/1280⟩
def center3141 : GaussianRat :=
  ⟨124838069/1000000000, -64141351/250000000⟩
def contact3141 : RatBall := localContactBall tau3141 center3141
def work3141 : RoundedTauEval :=
  evalTau precision tau3141 contact3141 logTwoBall

theorem center_sq3141 : (center3141.re : ℝ)^2 +
    (center3141.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3141]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3141 : work3141.theta.ok = true ∧
    work3141.jac.invOK = true ∧ acceptsUnitSq work3141.out = true := by decide +kernel

def cell3141 : CellCertificate where
  tauBall := tau3141
  contactCenter := center3141
  contactBall := contact3141
  work := work3141
  center_sq := center_sq3141
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3141.1
  jac_ok := checks3141.2.1
  accepted := checks3141.2.2

def tau3142 : RatBall :=
  ⟨⟨103/640, -233/640⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0392


