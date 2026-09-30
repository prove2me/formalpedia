-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0151
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0151
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:08:24.641913+00:00
-- url     : https://prove2.me/theorems/5be42396-1b4d-4cfb-ac2b-5e7e7ae277c5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0151` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0151` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0151` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0151 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0151.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0151 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0151

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1208 : RatBall :=
  ⟨⟨-69/320, -21/64⟩, 3/640⟩
def center1208 : GaussianRat :=
  ⟨-81980819/500000000, -223513477/1000000000⟩
def contact1208 : RatBall := localContactBall tau1208 center1208
def work1208 : RoundedTauEval :=
  evalTau precision tau1208 contact1208 logTwoBall

theorem center_sq1208 : (center1208.re : ℝ)^2 +
    (center1208.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1208]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1208 : work1208.theta.ok = true ∧
    work1208.jac.invOK = true ∧ acceptsUnitSq work1208.out = true := by decide +kernel

def cell1208 : CellCertificate where
  tauBall := tau1208
  contactCenter := center1208
  contactBall := contact1208
  work := work1208
  center_sq := center_sq1208
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1208.1
  jac_ok := checks1208.2.1
  accepted := checks1208.2.2

def tau1209 : RatBall :=
  ⟨⟨-67/320, -107/320⟩, 3/640⟩
def center1209 : GaussianRat :=
  ⟨-160137389/1000000000, -228757569/1000000000⟩
def contact1209 : RatBall := localContactBall tau1209 center1209
def work1209 : RoundedTauEval :=
  evalTau precision tau1209 contact1209 logTwoBall

theorem center_sq1209 : (center1209.re : ℝ)^2 +
    (center1209.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1209]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1209 : work1209.theta.ok = true ∧
    work1209.jac.invOK = true ∧ acceptsUnitSq work1209.out = true := by decide +kernel

def cell1209 : CellCertificate where
  tauBall := tau1209
  contactCenter := center1209
  contactBall := contact1209
  work := work1209
  center_sq := center_sq1209
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1209.1
  jac_ok := checks1209.2.1
  accepted := checks1209.2.2

def tau1210 : RatBall :=
  ⟨⟨-13/64, -107/320⟩, 3/640⟩
def center1210 : GaussianRat :=
  ⟨-77788111/500000000, -229460827/1000000000⟩
def contact1210 : RatBall := localContactBall tau1210 center1210
def work1210 : RoundedTauEval :=
  evalTau precision tau1210 contact1210 logTwoBall

theorem center_sq1210 : (center1210.re : ℝ)^2 +
    (center1210.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1210]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1210 : work1210.theta.ok = true ∧
    work1210.jac.invOK = true ∧ acceptsUnitSq work1210.out = true := by decide +kernel

def cell1210 : CellCertificate where
  tauBall := tau1210
  contactCenter := center1210
  contactBall := contact1210
  work := work1210
  center_sq := center_sq1210
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1210.1
  jac_ok := checks1210.2.1
  accepted := checks1210.2.2

def tau1211 : RatBall :=
  ⟨⟨-67/320, -21/64⟩, 3/640⟩
def center1211 : GaussianRat :=
  ⟨-79717703/500000000, -224213933/1000000000⟩
def contact1211 : RatBall := localContactBall tau1211 center1211
def work1211 : RoundedTauEval :=
  evalTau precision tau1211 contact1211 logTwoBall

theorem center_sq1211 : (center1211.re : ℝ)^2 +
    (center1211.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1211]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1211 : work1211.theta.ok = true ∧
    work1211.jac.invOK = true ∧ acceptsUnitSq work1211.out = true := by decide +kernel

def cell1211 : CellCertificate where
  tauBall := tau1211
  contactCenter := center1211
  contactBall := contact1211
  work := work1211
  center_sq := center_sq1211
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1211.1
  jac_ok := checks1211.2.1
  accepted := checks1211.2.2

def tau1212 : RatBall :=
  ⟨⟨-13/64, -21/64⟩, 3/640⟩
def center1212 : GaussianRat :=
  ⟨-30978099/200000000, -224898511/1000000000⟩
def contact1212 : RatBall := localContactBall tau1212 center1212
def work1212 : RoundedTauEval :=
  evalTau precision tau1212 contact1212 logTwoBall

theorem center_sq1212 : (center1212.re : ℝ)^2 +
    (center1212.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1212]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1212 : work1212.theta.ok = true ∧
    work1212.jac.invOK = true ∧ acceptsUnitSq work1212.out = true := by decide +kernel

def cell1212 : CellCertificate where
  tauBall := tau1212
  contactCenter := center1212
  contactBall := contact1212
  work := work1212
  center_sq := center_sq1212
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1212.1
  jac_ok := checks1212.2.1
  accepted := checks1212.2.2

def tau1213 : RatBall :=
  ⟨⟨-77/320, -103/320⟩, 3/640⟩
def center1213 : GaussianRat :=
  ⟨-36223107/200000000, -108064747/500000000⟩
def contact1213 : RatBall := localContactBall tau1213 center1213
def work1213 : RoundedTauEval :=
  evalTau precision tau1213 contact1213 logTwoBall

theorem center_sq1213 : (center1213.re : ℝ)^2 +
    (center1213.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1213]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1213 : work1213.theta.ok = true ∧
    work1213.jac.invOK = true ∧ acceptsUnitSq work1213.out = true := by decide +kernel

def cell1213 : CellCertificate where
  tauBall := tau1213
  contactCenter := center1213
  contactBall := contact1213
  work := work1213
  center_sq := center_sq1213
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1213.1
  jac_ok := checks1213.2.1
  accepted := checks1213.2.2

def tau1214 : RatBall :=
  ⟨⟨-79/320, -101/320⟩, 3/640⟩
def center1214 : GaussianRat :=
  ⟨-92389531/500000000, -210978373/1000000000⟩
def contact1214 : RatBall := localContactBall tau1214 center1214
def work1214 : RoundedTauEval :=
  evalTau precision tau1214 contact1214 logTwoBall

theorem center_sq1214 : (center1214.re : ℝ)^2 +
    (center1214.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1214]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1214 : work1214.theta.ok = true ∧
    work1214.jac.invOK = true ∧ acceptsUnitSq work1214.out = true := by decide +kernel

def cell1214 : CellCertificate where
  tauBall := tau1214
  contactCenter := center1214
  contactBall := contact1214
  work := work1214
  center_sq := center_sq1214
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1214.1
  jac_ok := checks1214.2.1
  accepted := checks1214.2.2

def tau1215 : RatBall :=
  ⟨⟨-77/320, -101/320⟩, 3/640⟩
def center1215 : GaussianRat :=
  ⟨-45094603/250000000, -105856123/500000000⟩
def contact1215 : RatBall := localContactBall tau1215 center1215
def work1215 : RoundedTauEval :=
  evalTau precision tau1215 contact1215 logTwoBall

theorem center_sq1215 : (center1215.re : ℝ)^2 +
    (center1215.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1215]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1215 : work1215.theta.ok = true ∧
    work1215.jac.invOK = true ∧ acceptsUnitSq work1215.out = true := by decide +kernel

def cell1215 : CellCertificate where
  tauBall := tau1215
  contactCenter := center1215
  contactBall := contact1215
  work := work1215
  center_sq := center_sq1215
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1215.1
  jac_ok := checks1215.2.1
  accepted := checks1215.2.2

def cells : List CellCertificate := [cell1208, cell1209, cell1210, cell1211, cell1212, cell1213, cell1214, cell1215]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0151

end


