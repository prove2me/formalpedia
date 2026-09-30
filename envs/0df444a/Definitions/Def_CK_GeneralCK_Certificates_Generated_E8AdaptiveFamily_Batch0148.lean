-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0148
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0148
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:33:45.410249+00:00
-- url     : https://prove2.me/theorems/c30f82c5-a046-4e18-85ca-4338425fb5b6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0148` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0148` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0148` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0148 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0148.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0148 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0148

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1184 : RatBall :=
  ⟨⟨33/160, 43/160⟩, 3/320⟩
def center1184 : GaussianRat :=
  ⟨151447357/1000000000, 91026767/500000000⟩
def contact1184 : RatBall := localContactBall tau1184 center1184
def work1184 : RoundedTauEval :=
  evalTau precision tau1184 contact1184 logTwoBall

theorem center_sq1184 : (center1184.re : ℝ)^2 +
    (center1184.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1184]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1184 : work1184.theta.ok = true ∧
    work1184.jac.invOK = true ∧ acceptsUnitSq work1184.out = true := by decide +kernel

def cell1184 : CellCertificate where
  tauBall := tau1184
  contactCenter := center1184
  contactBall := contact1184
  work := work1184
  center_sq := center_sq1184
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1184.1
  jac_ok := checks1184.2.1
  accepted := checks1184.2.2

def tau1185 : RatBall :=
  ⟨⟨7/32, 43/160⟩, 3/320⟩
def center1185 : GaussianRat :=
  ⟨160233593/1000000000, 180980837/1000000000⟩
def contact1185 : RatBall := localContactBall tau1185 center1185
def work1185 : RoundedTauEval :=
  evalTau precision tau1185 contact1185 logTwoBall

theorem center_sq1185 : (center1185.re : ℝ)^2 +
    (center1185.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1185]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1185 : work1185.theta.ok = true ∧
    work1185.jac.invOK = true ∧ acceptsUnitSq work1185.out = true := by decide +kernel

def cell1185 : CellCertificate where
  tauBall := tau1185
  contactCenter := center1185
  contactBall := contact1185
  work := work1185
  center_sq := center_sq1185
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1185.1
  jac_ok := checks1185.2.1
  accepted := checks1185.2.2

def tau1186 : RatBall :=
  ⟨⟨37/160, 41/160⟩, 3/320⟩
def center1186 : GaussianRat :=
  ⟨167843761/1000000000, 171194117/1000000000⟩
def contact1186 : RatBall := localContactBall tau1186 center1186
def work1186 : RoundedTauEval :=
  evalTau precision tau1186 contact1186 logTwoBall

theorem center_sq1186 : (center1186.re : ℝ)^2 +
    (center1186.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1186]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1186 : work1186.theta.ok = true ∧
    work1186.jac.invOK = true ∧ acceptsUnitSq work1186.out = true := by decide +kernel

def cell1186 : CellCertificate where
  tauBall := tau1186
  contactCenter := center1186
  contactBall := contact1186
  work := work1186
  center_sq := center_sq1186
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1186.1
  jac_ok := checks1186.2.1
  accepted := checks1186.2.2

def tau1187 : RatBall :=
  ⟨⟨39/160, 41/160⟩, 3/320⟩
def center1187 : GaussianRat :=
  ⟨44113519/250000000, 170094077/1000000000⟩
def contact1187 : RatBall := localContactBall tau1187 center1187
def work1187 : RoundedTauEval :=
  evalTau precision tau1187 contact1187 logTwoBall

theorem center_sq1187 : (center1187.re : ℝ)^2 +
    (center1187.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1187]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1187 : work1187.theta.ok = true ∧
    work1187.jac.invOK = true ∧ acceptsUnitSq work1187.out = true := by decide +kernel

def cell1187 : CellCertificate where
  tauBall := tau1187
  contactCenter := center1187
  contactBall := contact1187
  work := work1187
  center_sq := center_sq1187
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1187.1
  jac_ok := checks1187.2.1
  accepted := checks1187.2.2

def tau1188 : RatBall :=
  ⟨⟨37/160, 43/160⟩, 3/320⟩
def center1188 : GaussianRat :=
  ⟨84477561/500000000, 89929857/500000000⟩
def contact1188 : RatBall := localContactBall tau1188 center1188
def work1188 : RoundedTauEval :=
  evalTau precision tau1188 contact1188 logTwoBall

theorem center_sq1188 : (center1188.re : ℝ)^2 +
    (center1188.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1188]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1188 : work1188.theta.ok = true ∧
    work1188.jac.invOK = true ∧ acceptsUnitSq work1188.out = true := by decide +kernel

def cell1188 : CellCertificate where
  tauBall := tau1188
  contactCenter := center1188
  contactBall := contact1188
  work := work1188
  center_sq := center_sq1188
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1188.1
  jac_ok := checks1188.2.1
  accepted := checks1188.2.2

def tau1189 : RatBall :=
  ⟨⟨39/160, 43/160⟩, 3/320⟩
def center1189 : GaussianRat :=
  ⟨177609433/1000000000, 178692329/1000000000⟩
def contact1189 : RatBall := localContactBall tau1189 center1189
def work1189 : RoundedTauEval :=
  evalTau precision tau1189 contact1189 logTwoBall

theorem center_sq1189 : (center1189.re : ℝ)^2 +
    (center1189.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1189]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1189 : work1189.theta.ok = true ∧
    work1189.jac.invOK = true ∧ acceptsUnitSq work1189.out = true := by decide +kernel

def cell1189 : CellCertificate where
  tauBall := tau1189
  contactCenter := center1189
  contactBall := contact1189
  work := work1189
  center_sq := center_sq1189
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1189.1
  jac_ok := checks1189.2.1
  accepted := checks1189.2.2

def tau1190 : RatBall :=
  ⟨⟨33/160, 9/32⟩, 3/320⟩
def center1190 : GaussianRat :=
  ⟨9532907/62500000, 95448491/500000000⟩
def contact1190 : RatBall := localContactBall tau1190 center1190
def work1190 : RoundedTauEval :=
  evalTau precision tau1190 contact1190 logTwoBall

theorem center_sq1190 : (center1190.re : ℝ)^2 +
    (center1190.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1190]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1190 : work1190.theta.ok = true ∧
    work1190.jac.invOK = true ∧ acceptsUnitSq work1190.out = true := by decide +kernel

def cell1190 : CellCertificate where
  tauBall := tau1190
  contactCenter := center1190
  contactBall := contact1190
  work := work1190
  center_sq := center_sq1190
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1190.1
  jac_ok := checks1190.2.1
  accepted := checks1190.2.2

def tau1191 : RatBall :=
  ⟨⟨7/32, 9/32⟩, 3/320⟩
def center1191 : GaussianRat :=
  ⟨32272717/200000000, 189759799/1000000000⟩
def contact1191 : RatBall := localContactBall tau1191 center1191
def work1191 : RoundedTauEval :=
  evalTau precision tau1191 contact1191 logTwoBall

theorem center_sq1191 : (center1191.re : ℝ)^2 +
    (center1191.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1191]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1191 : work1191.theta.ok = true ∧
    work1191.jac.invOK = true ∧ acceptsUnitSq work1191.out = true := by decide +kernel

def cell1191 : CellCertificate where
  tauBall := tau1191
  contactCenter := center1191
  contactBall := contact1191
  work := work1191
  center_sq := center_sq1191
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1191.1
  jac_ok := checks1191.2.1
  accepted := checks1191.2.2

def cells : List CellCertificate := [cell1184, cell1185, cell1186, cell1187, cell1188, cell1189, cell1190, cell1191]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0148

end


