-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0153
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0153
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:44:48.514204+00:00
-- url     : https://prove2.me/theorems/eca278f5-6dc6-4b23-8765-6b8371ec9929
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0153` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0153` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0153` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0153 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0153.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0153 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0153

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1224 : RatBall :=
  ⟨⟨-15/64, -99/320⟩, 3/640⟩
def center1224 : GaussianRat :=
  ⟨-35050807/200000000, -8320383/40000000⟩
def contact1224 : RatBall := localContactBall tau1224 center1224
def work1224 : RoundedTauEval :=
  evalTau precision tau1224 contact1224 logTwoBall

theorem center_sq1224 : (center1224.re : ℝ)^2 +
    (center1224.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1224]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1224 : work1224.theta.ok = true ∧
    work1224.jac.invOK = true ∧ acceptsUnitSq work1224.out = true := by decide +kernel

def cell1224 : CellCertificate where
  tauBall := tau1224
  contactCenter := center1224
  contactBall := contact1224
  work := work1224
  center_sq := center_sq1224
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1224.1
  jac_ok := checks1224.2.1
  accepted := checks1224.2.2

def tau1225 : RatBall :=
  ⟨⟨-73/320, -99/320⟩, 3/640⟩
def center1225 : GaussianRat :=
  ⟨-42707047/250000000, -20869737/100000000⟩
def contact1225 : RatBall := localContactBall tau1225 center1225
def work1225 : RoundedTauEval :=
  evalTau precision tau1225 contact1225 logTwoBall

theorem center_sq1225 : (center1225.re : ℝ)^2 +
    (center1225.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1225]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1225 : work1225.theta.ok = true ∧
    work1225.jac.invOK = true ∧ acceptsUnitSq work1225.out = true := by decide +kernel

def cell1225 : CellCertificate where
  tauBall := tau1225
  contactCenter := center1225
  contactBall := contact1225
  work := work1225
  center_sq := center_sq1225
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1225.1
  jac_ok := checks1225.2.1
  accepted := checks1225.2.2

def tau1226 : RatBall :=
  ⟨⟨-15/64, -97/320⟩, 3/640⟩
def center1226 : GaussianRat :=
  ⟨-87284451/500000000, -101799907/500000000⟩
def contact1226 : RatBall := localContactBall tau1226 center1226
def work1226 : RoundedTauEval :=
  evalTau precision tau1226 contact1226 logTwoBall

theorem center_sq1226 : (center1226.re : ℝ)^2 +
    (center1226.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1226]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1226 : work1226.theta.ok = true ∧
    work1226.jac.invOK = true ∧ acceptsUnitSq work1226.out = true := by decide +kernel

def cell1226 : CellCertificate where
  tauBall := tau1226
  contactCenter := center1226
  contactBall := contact1226
  work := work1226
  center_sq := center_sq1226
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1226.1
  jac_ok := checks1226.2.1
  accepted := checks1226.2.2

def tau1227 : RatBall :=
  ⟨⟨-73/320, -97/320⟩, 3/640⟩
def center1227 : GaussianRat :=
  ⟨-42539121/250000000, -204268971/1000000000⟩
def contact1227 : RatBall := localContactBall tau1227 center1227
def work1227 : RoundedTauEval :=
  evalTau precision tau1227 contact1227 logTwoBall

theorem center_sq1227 : (center1227.re : ℝ)^2 +
    (center1227.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1227]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1227 : work1227.theta.ok = true ∧
    work1227.jac.invOK = true ∧ acceptsUnitSq work1227.out = true := by decide +kernel

def cell1227 : CellCertificate where
  tauBall := tau1227
  contactCenter := center1227
  contactBall := contact1227
  work := work1227
  center_sq := center_sq1227
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1227.1
  jac_ok := checks1227.2.1
  accepted := checks1227.2.2

def tau1228 : RatBall :=
  ⟨⟨-71/320, -103/320⟩, 3/640⟩
def center1228 : GaussianRat :=
  ⟨-83877437/500000000, -218307477/1000000000⟩
def contact1228 : RatBall := localContactBall tau1228 center1228
def work1228 : RoundedTauEval :=
  evalTau precision tau1228 contact1228 logTwoBall

theorem center_sq1228 : (center1228.re : ℝ)^2 +
    (center1228.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1228]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1228 : work1228.theta.ok = true ∧
    work1228.jac.invOK = true ∧ acceptsUnitSq work1228.out = true := by decide +kernel

def cell1228 : CellCertificate where
  tauBall := tau1228
  contactCenter := center1228
  contactBall := contact1228
  work := work1228
  center_sq := center_sq1228
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1228.1
  jac_ok := checks1228.2.1
  accepted := checks1228.2.2

def tau1229 : RatBall :=
  ⟨⟨-69/320, -103/320⟩, 3/640⟩
def center1229 : GaussianRat :=
  ⟨-40815707/250000000, -219004401/1000000000⟩
def contact1229 : RatBall := localContactBall tau1229 center1229
def work1229 : RoundedTauEval :=
  evalTau precision tau1229 contact1229 logTwoBall

theorem center_sq1229 : (center1229.re : ℝ)^2 +
    (center1229.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1229]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1229 : work1229.theta.ok = true ∧
    work1229.jac.invOK = true ∧ acceptsUnitSq work1229.out = true := by decide +kernel

def cell1229 : CellCertificate where
  tauBall := tau1229
  contactCenter := center1229
  contactBall := contact1229
  work := work1229
  center_sq := center_sq1229
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1229.1
  jac_ok := checks1229.2.1
  accepted := checks1229.2.2

def tau1230 : RatBall :=
  ⟨⟨-71/320, -101/320⟩, 3/640⟩
def center1230 : GaussianRat :=
  ⟨-167059951/1000000000, -10691611/50000000⟩
def contact1230 : RatBall := localContactBall tau1230 center1230
def work1230 : RoundedTauEval :=
  evalTau precision tau1230 contact1230 logTwoBall

theorem center_sq1230 : (center1230.re : ℝ)^2 +
    (center1230.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1230]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1230 : work1230.theta.ok = true ∧
    work1230.jac.invOK = true ∧ acceptsUnitSq work1230.out = true := by decide +kernel

def cell1230 : CellCertificate where
  tauBall := tau1230
  contactCenter := center1230
  contactBall := contact1230
  work := work1230
  center_sq := center_sq1230
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1230.1
  jac_ok := checks1230.2.1
  accepted := checks1230.2.2

def tau1231 : RatBall :=
  ⟨⟨-69/320, -101/320⟩, 3/640⟩
def center1231 : GaussianRat :=
  ⟨-32516539/200000000, -26813809/125000000⟩
def contact1231 : RatBall := localContactBall tau1231 center1231
def work1231 : RoundedTauEval :=
  evalTau precision tau1231 contact1231 logTwoBall

theorem center_sq1231 : (center1231.re : ℝ)^2 +
    (center1231.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1231]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1231 : work1231.theta.ok = true ∧
    work1231.jac.invOK = true ∧ acceptsUnitSq work1231.out = true := by decide +kernel

def cell1231 : CellCertificate where
  tauBall := tau1231
  contactCenter := center1231
  contactBall := contact1231
  work := work1231
  center_sq := center_sq1231
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1231.1
  jac_ok := checks1231.2.1
  accepted := checks1231.2.2

def cells : List CellCertificate := [cell1224, cell1225, cell1226, cell1227, cell1228, cell1229, cell1230, cell1231]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0153

end


