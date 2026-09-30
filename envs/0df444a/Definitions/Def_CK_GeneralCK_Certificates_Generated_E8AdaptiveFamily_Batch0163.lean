-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0163
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0163
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:10:15.816468+00:00
-- url     : https://prove2.me/theorems/1765c096-ceb4-4197-8831-713703470a55
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0163` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0163` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0163` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0163 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0163.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0163 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0163

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1304 : RatBall :=
  ⟨⟨-91/320, -83/320⟩, 3/640⟩
def center1304 : GaussianRat :=
  ⟨-204274783/1000000000, -168328783/1000000000⟩
def contact1304 : RatBall := localContactBall tau1304 center1304
def work1304 : RoundedTauEval :=
  evalTau precision tau1304 contact1304 logTwoBall

theorem center_sq1304 : (center1304.re : ℝ)^2 +
    (center1304.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1304]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1304 : work1304.theta.ok = true ∧
    work1304.jac.invOK = true ∧ acceptsUnitSq work1304.out = true := by decide +kernel

def cell1304 : CellCertificate where
  tauBall := tau1304
  contactCenter := center1304
  contactBall := contact1304
  work := work1304
  center_sq := center_sq1304
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1304.1
  jac_ok := checks1304.2.1
  accepted := checks1304.2.2

def tau1305 : RatBall :=
  ⟨⟨-89/320, -83/320⟩, 3/640⟩
def center1305 : GaussianRat :=
  ⟨-100043853/500000000, -84478333/500000000⟩
def contact1305 : RatBall := localContactBall tau1305 center1305
def work1305 : RoundedTauEval :=
  evalTau precision tau1305 contact1305 logTwoBall

theorem center_sq1305 : (center1305.re : ℝ)^2 +
    (center1305.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1305]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1305 : work1305.theta.ok = true ∧
    work1305.jac.invOK = true ∧ acceptsUnitSq work1305.out = true := by decide +kernel

def cell1305 : CellCertificate where
  tauBall := tau1305
  contactCenter := center1305
  contactBall := contact1305
  work := work1305
  center_sq := center_sq1305
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1305.1
  jac_ok := checks1305.2.1
  accepted := checks1305.2.2

def tau1306 : RatBall :=
  ⟨⟨-91/320, -81/320⟩, 3/640⟩
def center1306 : GaussianRat :=
  ⟨-101825843/500000000, -82077687/500000000⟩
def contact1306 : RatBall := localContactBall tau1306 center1306
def work1306 : RoundedTauEval :=
  evalTau precision tau1306 contact1306 logTwoBall

theorem center_sq1306 : (center1306.re : ℝ)^2 +
    (center1306.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1306]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1306 : work1306.theta.ok = true ∧
    work1306.jac.invOK = true ∧ acceptsUnitSq work1306.out = true := by decide +kernel

def cell1306 : CellCertificate where
  tauBall := tau1306
  contactCenter := center1306
  contactBall := contact1306
  work := work1306
  center_sq := center_sq1306
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1306.1
  jac_ok := checks1306.2.1
  accepted := checks1306.2.2

def tau1307 : RatBall :=
  ⟨⟨-89/320, -81/320⟩, 3/640⟩
def center1307 : GaussianRat :=
  ⟨-199473497/1000000000, -41191221/250000000⟩
def contact1307 : RatBall := localContactBall tau1307 center1307
def work1307 : RoundedTauEval :=
  evalTau precision tau1307 contact1307 logTwoBall

theorem center_sq1307 : (center1307.re : ℝ)^2 +
    (center1307.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1307]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1307 : work1307.theta.ok = true ∧
    work1307.jac.invOK = true ∧ acceptsUnitSq work1307.out = true := by decide +kernel

def cell1307 : CellCertificate where
  tauBall := tau1307
  contactCenter := center1307
  contactBall := contact1307
  work := work1307
  center_sq := center_sq1307
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1307.1
  jac_ok := checks1307.2.1
  accepted := checks1307.2.2

def tau1308 : RatBall :=
  ⟨⟨-87/320, -87/320⟩, 3/640⟩
def center1308 : GaussianRat :=
  ⟨-19714711/100000000, -178023711/1000000000⟩
def contact1308 : RatBall := localContactBall tau1308 center1308
def work1308 : RoundedTauEval :=
  evalTau precision tau1308 contact1308 logTwoBall

theorem center_sq1308 : (center1308.re : ℝ)^2 +
    (center1308.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1308]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1308 : work1308.theta.ok = true ∧
    work1308.jac.invOK = true ∧ acceptsUnitSq work1308.out = true := by decide +kernel

def cell1308 : CellCertificate where
  tauBall := tau1308
  contactCenter := center1308
  contactBall := contact1308
  work := work1308
  center_sq := center_sq1308
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1308.1
  jac_ok := checks1308.2.1
  accepted := checks1308.2.2

def tau1309 : RatBall :=
  ⟨⟨-17/64, -87/320⟩, 3/640⟩
def center1309 : GaussianRat :=
  ⟨-192903929/1000000000, -35733937/200000000⟩
def contact1309 : RatBall := localContactBall tau1309 center1309
def work1309 : RoundedTauEval :=
  evalTau precision tau1309 contact1309 logTwoBall

theorem center_sq1309 : (center1309.re : ℝ)^2 +
    (center1309.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1309]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1309 : work1309.theta.ok = true ∧
    work1309.jac.invOK = true ∧ acceptsUnitSq work1309.out = true := by decide +kernel

def cell1309 : CellCertificate where
  tauBall := tau1309
  contactCenter := center1309
  contactBall := contact1309
  work := work1309
  center_sq := center_sq1309
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1309.1
  jac_ok := checks1309.2.1
  accepted := checks1309.2.2

def tau1310 : RatBall :=
  ⟨⟨-87/320, -17/64⟩, 3/640⟩
def center1310 : GaussianRat :=
  ⟨-98252729/500000000, -34758949/200000000⟩
def contact1310 : RatBall := localContactBall tau1310 center1310
def work1310 : RoundedTauEval :=
  evalTau precision tau1310 contact1310 logTwoBall

theorem center_sq1310 : (center1310.re : ℝ)^2 +
    (center1310.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1310]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1310 : work1310.theta.ok = true ∧
    work1310.jac.invOK = true ∧ acceptsUnitSq work1310.out = true := by decide +kernel

def cell1310 : CellCertificate where
  tauBall := tau1310
  contactCenter := center1310
  contactBall := contact1310
  work := work1310
  center_sq := center_sq1310
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1310.1
  jac_ok := checks1310.2.1
  accepted := checks1310.2.2

def tau1311 : RatBall :=
  ⟨⟨-17/64, -17/64⟩, 3/640⟩
def center1311 : GaussianRat :=
  ⟨-12017011/62500000, -17442227/100000000⟩
def contact1311 : RatBall := localContactBall tau1311 center1311
def work1311 : RoundedTauEval :=
  evalTau precision tau1311 contact1311 logTwoBall

theorem center_sq1311 : (center1311.re : ℝ)^2 +
    (center1311.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1311]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1311 : work1311.theta.ok = true ∧
    work1311.jac.invOK = true ∧ acceptsUnitSq work1311.out = true := by decide +kernel

def cell1311 : CellCertificate where
  tauBall := tau1311
  contactCenter := center1311
  contactBall := contact1311
  work := work1311
  center_sq := center_sq1311
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1311.1
  jac_ok := checks1311.2.1
  accepted := checks1311.2.2

def cells : List CellCertificate := [cell1304, cell1305, cell1306, cell1307, cell1308, cell1309, cell1310, cell1311]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0163

end


