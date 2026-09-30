-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0152
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0152
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:54:56.767815+00:00
-- url     : https://prove2.me/theorems/40ab3df5-a99c-4d13-bdfd-f0ff19353072
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0152` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0152` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0152` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0152 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0152.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0152 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0152

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1216 : RatBall :=
  ⟨⟨-15/64, -103/320⟩, 3/640⟩
def center1216 : GaussianRat :=
  ⟨-44170389/250000000, -43373931/200000000⟩
def contact1216 : RatBall := localContactBall tau1216 center1216
def work1216 : RoundedTauEval :=
  evalTau precision tau1216 contact1216 logTwoBall

theorem center_sq1216 : (center1216.re : ℝ)^2 +
    (center1216.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1216]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1216 : work1216.theta.ok = true ∧
    work1216.jac.invOK = true ∧ acceptsUnitSq work1216.out = true := by decide +kernel

def cell1216 : CellCertificate where
  tauBall := tau1216
  contactCenter := center1216
  contactBall := contact1216
  work := work1216
  center_sq := center_sq1216
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1216.1
  jac_ok := checks1216.2.1
  accepted := checks1216.2.2

def tau1217 : RatBall :=
  ⟨⟨-73/320, -103/320⟩, 3/640⟩
def center1217 : GaussianRat :=
  ⟨-34445579/200000000, -217595773/1000000000⟩
def contact1217 : RatBall := localContactBall tau1217 center1217
def work1217 : RoundedTauEval :=
  evalTau precision tau1217 contact1217 logTwoBall

theorem center_sq1217 : (center1217.re : ℝ)^2 +
    (center1217.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1217]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1217 : work1217.theta.ok = true ∧
    work1217.jac.invOK = true ∧ acceptsUnitSq work1217.out = true := by decide +kernel

def cell1217 : CellCertificate where
  tauBall := tau1217
  contactCenter := center1217
  contactBall := contact1217
  work := work1217
  center_sq := center_sq1217
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1217.1
  jac_ok := checks1217.2.1
  accepted := checks1217.2.2

def tau1218 : RatBall :=
  ⟨⟨-15/64, -101/320⟩, 3/640⟩
def center1218 : GaussianRat :=
  ⟨-21994767/125000000, -212432751/1000000000⟩
def contact1218 : RatBall := localContactBall tau1218 center1218
def work1218 : RoundedTauEval :=
  evalTau precision tau1218 contact1218 logTwoBall

theorem center_sq1218 : (center1218.re : ℝ)^2 +
    (center1218.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1218]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1218 : work1218.theta.ok = true ∧
    work1218.jac.invOK = true ∧ acceptsUnitSq work1218.out = true := by decide +kernel

def cell1218 : CellCertificate where
  tauBall := tau1218
  contactCenter := center1218
  contactBall := contact1218
  work := work1218
  center_sq := center_sq1218
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1218.1
  jac_ok := checks1218.2.1
  accepted := checks1218.2.2

def tau1219 : RatBall :=
  ⟨⟨-73/320, -101/320⟩, 3/640⟩
def center1219 : GaussianRat :=
  ⟨-85759271/500000000, -26642441/125000000⟩
def contact1219 : RatBall := localContactBall tau1219 center1219
def work1219 : RoundedTauEval :=
  evalTau precision tau1219 contact1219 logTwoBall

theorem center_sq1219 : (center1219.re : ℝ)^2 +
    (center1219.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1219]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1219 : work1219.theta.ok = true ∧
    work1219.jac.invOK = true ∧ acceptsUnitSq work1219.out = true := by decide +kernel

def cell1219 : CellCertificate where
  tauBall := tau1219
  contactCenter := center1219
  contactBall := contact1219
  work := work1219
  center_sq := center_sq1219
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1219.1
  jac_ok := checks1219.2.1
  accepted := checks1219.2.2

def tau1220 : RatBall :=
  ⟨⟨-79/320, -99/320⟩, 3/640⟩
def center1220 : GaussianRat :=
  ⟨-184048527/1000000000, -206594091/1000000000⟩
def contact1220 : RatBall := localContactBall tau1220 center1220
def work1220 : RoundedTauEval :=
  evalTau precision tau1220 contact1220 logTwoBall

theorem center_sq1220 : (center1220.re : ℝ)^2 +
    (center1220.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1220]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1220 : work1220.theta.ok = true ∧
    work1220.jac.invOK = true ∧ acceptsUnitSq work1220.out = true := by decide +kernel

def cell1220 : CellCertificate where
  tauBall := tau1220
  contactCenter := center1220
  contactBall := contact1220
  work := work1220
  center_sq := center_sq1220
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1220.1
  jac_ok := checks1220.2.1
  accepted := checks1220.2.2

def tau1221 : RatBall :=
  ⟨⟨-77/320, -99/320⟩, 3/640⟩
def center1221 : GaussianRat :=
  ⟨-179660917/1000000000, -207308367/1000000000⟩
def contact1221 : RatBall := localContactBall tau1221 center1221
def work1221 : RoundedTauEval :=
  evalTau precision tau1221 contact1221 logTwoBall

theorem center_sq1221 : (center1221.re : ℝ)^2 +
    (center1221.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1221]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1221 : work1221.theta.ok = true ∧
    work1221.jac.invOK = true ∧ acceptsUnitSq work1221.out = true := by decide +kernel

def cell1221 : CellCertificate where
  tauBall := tau1221
  contactCenter := center1221
  contactBall := contact1221
  work := work1221
  center_sq := center_sq1221
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1221.1
  jac_ok := checks1221.2.1
  accepted := checks1221.2.2

def tau1222 : RatBall :=
  ⟨⟨-79/320, -97/320⟩, 3/640⟩
def center1222 : GaussianRat :=
  ⟨-183337559/1000000000, -202222527/1000000000⟩
def contact1222 : RatBall := localContactBall tau1222 center1222
def work1222 : RoundedTauEval :=
  evalTau precision tau1222 contact1222 logTwoBall

theorem center_sq1222 : (center1222.re : ℝ)^2 +
    (center1222.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1222]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1222 : work1222.theta.ok = true ∧
    work1222.jac.invOK = true ∧ acceptsUnitSq work1222.out = true := by decide +kernel

def cell1222 : CellCertificate where
  tauBall := tau1222
  contactCenter := center1222
  contactBall := contact1222
  work := work1222
  center_sq := center_sq1222
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1222.1
  jac_ok := checks1222.2.1
  accepted := checks1222.2.2

def tau1223 : RatBall :=
  ⟨⟨-77/320, -97/320⟩, 3/640⟩
def center1223 : GaussianRat :=
  ⟨-35792539/200000000, -40583511/200000000⟩
def contact1223 : RatBall := localContactBall tau1223 center1223
def work1223 : RoundedTauEval :=
  evalTau precision tau1223 contact1223 logTwoBall

theorem center_sq1223 : (center1223.re : ℝ)^2 +
    (center1223.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1223]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1223 : work1223.theta.ok = true ∧
    work1223.jac.invOK = true ∧ acceptsUnitSq work1223.out = true := by decide +kernel

def cell1223 : CellCertificate where
  tauBall := tau1223
  contactCenter := center1223
  contactBall := contact1223
  work := work1223
  center_sq := center_sq1223
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1223.1
  jac_ok := checks1223.2.1
  accepted := checks1223.2.2

def cells : List CellCertificate := [cell1216, cell1217, cell1218, cell1219, cell1220, cell1221, cell1222, cell1223]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0152

end


