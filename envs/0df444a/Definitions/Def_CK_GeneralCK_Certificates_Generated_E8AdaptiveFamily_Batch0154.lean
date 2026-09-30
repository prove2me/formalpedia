-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0154
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0154
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:33:43.794284+00:00
-- url     : https://prove2.me/theorems/86388714-0efa-4aec-aead-244cf910a72a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0154` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0154` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0154` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0154 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0154.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0154 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0154

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1232 : RatBall :=
  ⟨⟨-67/320, -103/320⟩, 3/640⟩
def center1232 : GaussianRat :=
  ⟨-79376053/500000000, -109843089/500000000⟩
def contact1232 : RatBall := localContactBall tau1232 center1232
def work1232 : RoundedTauEval :=
  evalTau precision tau1232 contact1232 logTwoBall

theorem center_sq1232 : (center1232.re : ℝ)^2 +
    (center1232.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1232]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1232 : work1232.theta.ok = true ∧
    work1232.jac.invOK = true ∧ acceptsUnitSq work1232.out = true := by decide +kernel

def cell1232 : CellCertificate where
  tauBall := tau1232
  contactCenter := center1232
  contactBall := contact1232
  work := work1232
  center_sq := center_sq1232
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1232.1
  jac_ok := checks1232.2.1
  accepted := checks1232.2.2

def tau1233 : RatBall :=
  ⟨⟨-13/64, -103/320⟩, 3/640⟩
def center1233 : GaussianRat :=
  ⟨-154223071/1000000000, -110176223/500000000⟩
def contact1233 : RatBall := localContactBall tau1233 center1233
def work1233 : RoundedTauEval :=
  evalTau precision tau1233 contact1233 logTwoBall

theorem center_sq1233 : (center1233.re : ℝ)^2 +
    (center1233.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1233]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1233 : work1233.theta.ok = true ∧
    work1233.jac.invOK = true ∧ acceptsUnitSq work1233.out = true := by decide +kernel

def cell1233 : CellCertificate where
  tauBall := tau1233
  contactCenter := center1233
  contactBall := contact1233
  work := work1233
  center_sq := center_sq1233
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1233.1
  jac_ok := checks1233.2.1
  accepted := checks1233.2.2

def tau1234 : RatBall :=
  ⟨⟨-67/320, -101/320⟩, 3/640⟩
def center1234 : GaussianRat :=
  ⟨-158087121/1000000000, -215173931/1000000000⟩
def contact1234 : RatBall := localContactBall tau1234 center1234
def work1234 : RoundedTauEval :=
  evalTau precision tau1234 contact1234 logTwoBall

theorem center_sq1234 : (center1234.re : ℝ)^2 +
    (center1234.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1234]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1234 : work1234.theta.ok = true ∧
    work1234.jac.invOK = true ∧ acceptsUnitSq work1234.out = true := by decide +kernel

def cell1234 : CellCertificate where
  tauBall := tau1234
  contactCenter := center1234
  contactBall := contact1234
  work := work1234
  center_sq := center_sq1234
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1234.1
  jac_ok := checks1234.2.1
  accepted := checks1234.2.2

def tau1235 : RatBall :=
  ⟨⟨-13/64, -101/320⟩, 3/640⟩
def center1235 : GaussianRat :=
  ⟨-38393397/250000000, -26977781/125000000⟩
def contact1235 : RatBall := localContactBall tau1235 center1235
def work1235 : RoundedTauEval :=
  evalTau precision tau1235 contact1235 logTwoBall

theorem center_sq1235 : (center1235.re : ℝ)^2 +
    (center1235.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1235]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1235 : work1235.theta.ok = true ∧
    work1235.jac.invOK = true ∧ acceptsUnitSq work1235.out = true := by decide +kernel

def cell1235 : CellCertificate where
  tauBall := tau1235
  contactCenter := center1235
  contactBall := contact1235
  work := work1235
  center_sq := center_sq1235
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1235.1
  jac_ok := checks1235.2.1
  accepted := checks1235.2.2

def tau1236 : RatBall :=
  ⟨⟨-71/320, -99/320⟩, 3/640⟩
def center1236 : GaussianRat :=
  ⟨-83191847/500000000, -52342851/250000000⟩
def contact1236 : RatBall := localContactBall tau1236 center1236
def work1236 : RoundedTauEval :=
  evalTau precision tau1236 contact1236 logTwoBall

theorem center_sq1236 : (center1236.re : ℝ)^2 +
    (center1236.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1236]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1236 : work1236.theta.ok = true ∧
    work1236.jac.invOK = true ∧ acceptsUnitSq work1236.out = true := by decide +kernel

def cell1236 : CellCertificate where
  tauBall := tau1236
  contactCenter := center1236
  contactBall := contact1236
  work := work1236
  center_sq := center_sq1236
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1236.1
  jac_ok := checks1236.2.1
  accepted := checks1236.2.2

def tau1237 : RatBall :=
  ⟨⟨-69/320, -99/320⟩, 3/640⟩
def center1237 : GaussianRat :=
  ⟨-161920883/1000000000, -210031337/1000000000⟩
def contact1237 : RatBall := localContactBall tau1237 center1237
def work1237 : RoundedTauEval :=
  evalTau precision tau1237 contact1237 logTwoBall

theorem center_sq1237 : (center1237.re : ℝ)^2 +
    (center1237.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1237]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1237 : work1237.theta.ok = true ∧
    work1237.jac.invOK = true ∧ acceptsUnitSq work1237.out = true := by decide +kernel

def cell1237 : CellCertificate where
  tauBall := tau1237
  contactCenter := center1237
  contactBall := contact1237
  work := work1237
  center_sq := center_sq1237
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1237.1
  jac_ok := checks1237.2.1
  accepted := checks1237.2.2

def tau1238 : RatBall :=
  ⟨⟨-71/320, -97/320⟩, 3/640⟩
def center1238 : GaussianRat :=
  ⟨-41431439/250000000, -204924691/1000000000⟩
def contact1238 : RatBall := localContactBall tau1238 center1238
def work1238 : RoundedTauEval :=
  evalTau precision tau1238 contact1238 logTwoBall

theorem center_sq1238 : (center1238.re : ℝ)^2 +
    (center1238.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1238]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1238 : work1238.theta.ok = true ∧
    work1238.jac.invOK = true ∧ acceptsUnitSq work1238.out = true := by decide +kernel

def cell1238 : CellCertificate where
  tauBall := tau1238
  contactCenter := center1238
  contactBall := contact1238
  work := work1238
  center_sq := center_sq1238
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1238.1
  jac_ok := checks1238.2.1
  accepted := checks1238.2.2

def tau1239 : RatBall :=
  ⟨⟨-69/320, -97/320⟩, 3/640⟩
def center1239 : GaussianRat :=
  ⟨-161277047/1000000000, -51391661/250000000⟩
def contact1239 : RatBall := localContactBall tau1239 center1239
def work1239 : RoundedTauEval :=
  evalTau precision tau1239 contact1239 logTwoBall

theorem center_sq1239 : (center1239.re : ℝ)^2 +
    (center1239.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1239]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1239 : work1239.theta.ok = true ∧
    work1239.jac.invOK = true ∧ acceptsUnitSq work1239.out = true := by decide +kernel

def cell1239 : CellCertificate where
  tauBall := tau1239
  contactCenter := center1239
  contactBall := contact1239
  work := work1239
  center_sq := center_sq1239
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1239.1
  jac_ok := checks1239.2.1
  accepted := checks1239.2.2

def cells : List CellCertificate := [cell1232, cell1233, cell1234, cell1235, cell1236, cell1237, cell1238, cell1239]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0154

end


