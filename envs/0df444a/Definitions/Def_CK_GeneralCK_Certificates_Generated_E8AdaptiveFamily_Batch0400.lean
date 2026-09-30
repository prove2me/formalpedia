-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0400
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0400
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:01:36.814319+00:00
-- url     : https://prove2.me/theorems/4559d3c6-4882-481d-a82f-ce65e9c59e7e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0400` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0400` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0400` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0400 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0400.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0400 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0400

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3200 : RatBall :=
  ⟨⟨141/640, -43/128⟩, 3/1280⟩
def center3200 : GaussianRat :=
  ⟨84129393/500000000, -228617923/1000000000⟩
def contact3200 : RatBall := localContactBall tau3200 center3200
def work3200 : RoundedTauEval :=
  evalTau precision tau3200 contact3200 logTwoBall

theorem center_sq3200 : (center3200.re : ℝ)^2 +
    (center3200.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3200]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3200 : work3200.theta.ok = true ∧
    work3200.jac.invOK = true ∧ acceptsUnitSq work3200.out = true := by decide +kernel

def cell3200 : CellCertificate where
  tauBall := tau3200
  contactCenter := center3200
  contactBall := contact3200
  work := work3200
  center_sq := center_sq3200
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3200.1
  jac_ok := checks3200.2.1
  accepted := checks3200.2.2

def tau3201 : RatBall :=
  ⟨⟨141/640, -213/640⟩, 3/1280⟩
def center3201 : GaussianRat :=
  ⟨33577827/200000000, -28294879/125000000⟩
def contact3201 : RatBall := localContactBall tau3201 center3201
def work3201 : RoundedTauEval :=
  evalTau precision tau3201 contact3201 logTwoBall

theorem center_sq3201 : (center3201.re : ℝ)^2 +
    (center3201.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3201]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3201 : work3201.theta.ok = true ∧
    work3201.jac.invOK = true ∧ acceptsUnitSq work3201.out = true := by decide +kernel

def cell3201 : CellCertificate where
  tauBall := tau3201
  contactCenter := center3201
  contactBall := contact3201
  work := work3201
  center_sq := center_sq3201
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3201.1
  jac_ok := checks3201.2.1
  accepted := checks3201.2.2

def tau3202 : RatBall :=
  ⟨⟨143/640, -213/640⟩, 3/1280⟩
def center3202 : GaussianRat :=
  ⟨85071813/500000000, -28248739/125000000⟩
def contact3202 : RatBall := localContactBall tau3202 center3202
def work3202 : RoundedTauEval :=
  evalTau precision tau3202 contact3202 logTwoBall

theorem center_sq3202 : (center3202.re : ℝ)^2 +
    (center3202.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3202]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3202 : work3202.theta.ok = true ∧
    work3202.jac.invOK = true ∧ acceptsUnitSq work3202.out = true := by decide +kernel

def cell3202 : CellCertificate where
  tauBall := tau3202
  contactCenter := center3202
  contactBall := contact3202
  work := work3202
  center_sq := center_sq3202
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3202.1
  jac_ok := checks3202.2.1
  accepted := checks3202.2.2

def tau3203 : RatBall :=
  ⟨⟨149/640, -209/640⟩, 3/1280⟩
def center3203 : GaussianRat :=
  ⟨176122773/1000000000, -220393101/1000000000⟩
def contact3203 : RatBall := localContactBall tau3203 center3203
def work3203 : RoundedTauEval :=
  evalTau precision tau3203 contact3203 logTwoBall

theorem center_sq3203 : (center3203.re : ℝ)^2 +
    (center3203.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3203]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3203 : work3203.theta.ok = true ∧
    work3203.jac.invOK = true ∧ acceptsUnitSq work3203.out = true := by decide +kernel

def cell3203 : CellCertificate where
  tauBall := tau3203
  contactCenter := center3203
  contactBall := contact3203
  work := work3203
  center_sq := center_sq3203
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3203.1
  jac_ok := checks3203.2.1
  accepted := checks3203.2.2

def tau3204 : RatBall :=
  ⟨⟨-149/640, 209/640⟩, 3/1280⟩
def center3204 : GaussianRat :=
  ⟨-176122773/1000000000, 220393101/1000000000⟩
def contact3204 : RatBall := localContactBall tau3204 center3204
def work3204 : RoundedTauEval :=
  evalTau precision tau3204 contact3204 logTwoBall

theorem center_sq3204 : (center3204.re : ℝ)^2 +
    (center3204.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3204]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3204 : work3204.theta.ok = true ∧
    work3204.jac.invOK = true ∧ acceptsUnitSq work3204.out = true := by decide +kernel

def cell3204 : CellCertificate where
  tauBall := tau3204
  contactCenter := center3204
  contactBall := contact3204
  work := work3204
  center_sq := center_sq3204
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3204.1
  jac_ok := checks3204.2.1
  accepted := checks3204.2.2

def tau3205 : RatBall :=
  ⟨⟨-143/640, 213/640⟩, 3/1280⟩
def center3205 : GaussianRat :=
  ⟨-85071813/500000000, 28248739/125000000⟩
def contact3205 : RatBall := localContactBall tau3205 center3205
def work3205 : RoundedTauEval :=
  evalTau precision tau3205 contact3205 logTwoBall

theorem center_sq3205 : (center3205.re : ℝ)^2 +
    (center3205.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3205]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3205 : work3205.theta.ok = true ∧
    work3205.jac.invOK = true ∧ acceptsUnitSq work3205.out = true := by decide +kernel

def cell3205 : CellCertificate where
  tauBall := tau3205
  contactCenter := center3205
  contactBall := contact3205
  work := work3205
  center_sq := center_sq3205
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3205.1
  jac_ok := checks3205.2.1
  accepted := checks3205.2.2

def tau3206 : RatBall :=
  ⟨⟨-141/640, 213/640⟩, 3/1280⟩
def center3206 : GaussianRat :=
  ⟨-33577827/200000000, 28294879/125000000⟩
def contact3206 : RatBall := localContactBall tau3206 center3206
def work3206 : RoundedTauEval :=
  evalTau precision tau3206 contact3206 logTwoBall

theorem center_sq3206 : (center3206.re : ℝ)^2 +
    (center3206.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3206]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3206 : work3206.theta.ok = true ∧
    work3206.jac.invOK = true ∧ acceptsUnitSq work3206.out = true := by decide +kernel

def cell3206 : CellCertificate where
  tauBall := tau3206
  contactCenter := center3206
  contactBall := contact3206
  work := work3206
  center_sq := center_sq3206
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3206.1
  jac_ok := checks3206.2.1
  accepted := checks3206.2.2

def tau3207 : RatBall :=
  ⟨⟨-141/640, 43/128⟩, 3/1280⟩
def center3207 : GaussianRat :=
  ⟨-84129393/500000000, 228617923/1000000000⟩
def contact3207 : RatBall := localContactBall tau3207 center3207
def work3207 : RoundedTauEval :=
  evalTau precision tau3207 contact3207 logTwoBall

theorem center_sq3207 : (center3207.re : ℝ)^2 +
    (center3207.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3207]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3207 : work3207.theta.ok = true ∧
    work3207.jac.invOK = true ∧ acceptsUnitSq work3207.out = true := by decide +kernel

def cell3207 : CellCertificate where
  tauBall := tau3207
  contactCenter := center3207
  contactBall := contact3207
  work := work3207
  center_sq := center_sq3207
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3207.1
  jac_ok := checks3207.2.1
  accepted := checks3207.2.2

def cells : List CellCertificate := [cell3200, cell3201, cell3202, cell3203, cell3204, cell3205, cell3206, cell3207]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0400

end


