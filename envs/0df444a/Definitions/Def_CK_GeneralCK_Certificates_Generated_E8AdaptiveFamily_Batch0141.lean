-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0141
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0141
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:51:25.723325+00:00
-- url     : https://prove2.me/theorems/110befe5-f01a-4fa7-a112-9ab37b292636
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0141` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0141` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0141` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0141 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0141.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0141 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0141

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1128 : RatBall :=
  ⟨⟨11/160, 49/160⟩, 3/320⟩
def center1128 : GaussianRat :=
  ⟨52658297/1000000000, 109167283/500000000⟩
def contact1128 : RatBall := localContactBall tau1128 center1128
def work1128 : RoundedTauEval :=
  evalTau precision tau1128 contact1128 logTwoBall

theorem center_sq1128 : (center1128.re : ℝ)^2 +
    (center1128.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1128]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1128 : work1128.theta.ok = true ∧
    work1128.jac.invOK = true ∧ acceptsUnitSq work1128.out = true := by decide +kernel

def cell1128 : CellCertificate where
  tauBall := tau1128
  contactCenter := center1128
  contactBall := contact1128
  work := work1128
  center_sq := center_sq1128
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1128.1
  jac_ok := checks1128.2.1
  accepted := checks1128.2.2

def tau1129 : RatBall :=
  ⟨⟨9/160, 51/160⟩, 3/320⟩
def center1129 : GaussianRat :=
  ⟨21754011/500000000, 445983/1953125⟩
def contact1129 : RatBall := localContactBall tau1129 center1129
def work1129 : RoundedTauEval :=
  evalTau precision tau1129 contact1129 logTwoBall

theorem center_sq1129 : (center1129.re : ℝ)^2 +
    (center1129.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1129]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1129 : work1129.theta.ok = true ∧
    work1129.jac.invOK = true ∧ acceptsUnitSq work1129.out = true := by decide +kernel

def cell1129 : CellCertificate where
  tauBall := tau1129
  contactCenter := center1129
  contactBall := contact1129
  work := work1129
  center_sq := center_sq1129
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1129.1
  jac_ok := checks1129.2.1
  accepted := checks1129.2.2

def tau1130 : RatBall :=
  ⟨⟨11/160, 51/160⟩, 3/320⟩
def center1130 : GaussianRat :=
  ⟨53129867/1000000000, 56975307/250000000⟩
def contact1130 : RatBall := localContactBall tau1130 center1130
def work1130 : RoundedTauEval :=
  evalTau precision tau1130 contact1130 logTwoBall

theorem center_sq1130 : (center1130.re : ℝ)^2 +
    (center1130.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1130]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1130 : work1130.theta.ok = true ∧
    work1130.jac.invOK = true ∧ acceptsUnitSq work1130.out = true := by decide +kernel

def cell1130 : CellCertificate where
  tauBall := tau1130
  contactCenter := center1130
  contactBall := contact1130
  work := work1130
  center_sq := center_sq1130
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1130.1
  jac_ok := checks1130.2.1
  accepted := checks1130.2.2

def tau1131 : RatBall :=
  ⟨⟨13/160, 49/160⟩, 3/320⟩
def center1131 : GaussianRat :=
  ⟨3885599/62500000, 6807377/31250000⟩
def contact1131 : RatBall := localContactBall tau1131 center1131
def work1131 : RoundedTauEval :=
  evalTau precision tau1131 contact1131 logTwoBall

theorem center_sq1131 : (center1131.re : ℝ)^2 +
    (center1131.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1131]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1131 : work1131.theta.ok = true ∧
    work1131.jac.invOK = true ∧ acceptsUnitSq work1131.out = true := by decide +kernel

def cell1131 : CellCertificate where
  tauBall := tau1131
  contactCenter := center1131
  contactBall := contact1131
  work := work1131
  center_sq := center_sq1131
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1131.1
  jac_ok := checks1131.2.1
  accepted := checks1131.2.2

def tau1132 : RatBall :=
  ⟨⟨3/32, 49/160⟩, 3/320⟩
def center1132 : GaussianRat :=
  ⟨14329959/200000000, 108628837/500000000⟩
def contact1132 : RatBall := localContactBall tau1132 center1132
def work1132 : RoundedTauEval :=
  evalTau precision tau1132 contact1132 logTwoBall

theorem center_sq1132 : (center1132.re : ℝ)^2 +
    (center1132.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1132]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1132 : work1132.theta.ok = true ∧
    work1132.jac.invOK = true ∧ acceptsUnitSq work1132.out = true := by decide +kernel

def cell1132 : CellCertificate where
  tauBall := tau1132
  contactCenter := center1132
  contactBall := contact1132
  work := work1132
  center_sq := center_sq1132
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1132.1
  jac_ok := checks1132.2.1
  accepted := checks1132.2.2

def tau1133 : RatBall :=
  ⟨⟨13/160, 51/160⟩, 3/320⟩
def center1133 : GaussianRat :=
  ⟨2508961/40000000, 56843321/250000000⟩
def contact1133 : RatBall := localContactBall tau1133 center1133
def work1133 : RoundedTauEval :=
  evalTau precision tau1133 contact1133 logTwoBall

theorem center_sq1133 : (center1133.re : ℝ)^2 +
    (center1133.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1133]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1133 : work1133.theta.ok = true ∧
    work1133.jac.invOK = true ∧ acceptsUnitSq work1133.out = true := by decide +kernel

def cell1133 : CellCertificate where
  tauBall := tau1133
  contactCenter := center1133
  contactBall := contact1133
  work := work1133
  center_sq := center_sq1133
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1133.1
  jac_ok := checks1133.2.1
  accepted := checks1133.2.2

def tau1134 : RatBall :=
  ⟨⟨3/32, 51/160⟩, 3/320⟩
def center1134 : GaussianRat :=
  ⟨18071427/250000000, 113380411/500000000⟩
def contact1134 : RatBall := localContactBall tau1134 center1134
def work1134 : RoundedTauEval :=
  evalTau precision tau1134 contact1134 logTwoBall

theorem center_sq1134 : (center1134.re : ℝ)^2 +
    (center1134.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1134]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1134 : work1134.theta.ok = true ∧
    work1134.jac.invOK = true ∧ acceptsUnitSq work1134.out = true := by decide +kernel

def cell1134 : CellCertificate where
  tauBall := tau1134
  contactCenter := center1134
  contactBall := contact1134
  work := work1134
  center_sq := center_sq1134
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1134.1
  jac_ok := checks1134.2.1
  accepted := checks1134.2.2

def tau1135 : RatBall :=
  ⟨⟨9/160, 53/160⟩, 3/320⟩
def center1135 : GaussianRat :=
  ⟨43918333/1000000000, 238021713/1000000000⟩
def contact1135 : RatBall := localContactBall tau1135 center1135
def work1135 : RoundedTauEval :=
  evalTau precision tau1135 contact1135 logTwoBall

theorem center_sq1135 : (center1135.re : ℝ)^2 +
    (center1135.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1135]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1135 : work1135.theta.ok = true ∧
    work1135.jac.invOK = true ∧ acceptsUnitSq work1135.out = true := by decide +kernel

def cell1135 : CellCertificate where
  tauBall := tau1135
  contactCenter := center1135
  contactBall := contact1135
  work := work1135
  center_sq := center_sq1135
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1135.1
  jac_ok := checks1135.2.1
  accepted := checks1135.2.2

def cells : List CellCertificate := [cell1128, cell1129, cell1130, cell1131, cell1132, cell1133, cell1134, cell1135]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0141

end


