-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0143_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0143_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:25:25.766549+00:00
-- url     : https://prove2.me/theorems/1a550f01-51e3-43ef-8758-7b2b4ba7b063
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0143 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1144 : RatBall :=
  ⟨⟨19/160, 51/160⟩, 3/320⟩
def center1144 : GaussianRat :=
  ⟨18258621/200000000, 56322187/250000000⟩
def contact1144 : RatBall := localContactBall tau1144 center1144
def work1144 : RoundedTauEval :=
  evalTau precision tau1144 contact1144 logTwoBall

theorem center_sq1144 : (center1144.re : ℝ)^2 +
    (center1144.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1144]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1144 : work1144.theta.ok = true ∧
    work1144.jac.invOK = true ∧ acceptsUnitSq work1144.out = true := by decide +kernel

def cell1144 : CellCertificate where
  tauBall := tau1144
  contactCenter := center1144
  contactBall := contact1144
  work := work1144
  center_sq := center_sq1144
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1144.1
  jac_ok := checks1144.2.1
  accepted := checks1144.2.2

def tau1145 : RatBall :=
  ⟨⟨21/160, 49/160⟩, 3/320⟩
def center1145 : GaussianRat :=
  ⟨9985979/100000000, 43011679/200000000⟩
def contact1145 : RatBall := localContactBall tau1145 center1145
def work1145 : RoundedTauEval :=
  evalTau precision tau1145 contact1145 logTwoBall

theorem center_sq1145 : (center1145.re : ℝ)^2 +
    (center1145.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1145]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1145 : work1145.theta.ok = true ∧
    work1145.jac.invOK = true ∧ acceptsUnitSq work1145.out = true := by decide +kernel

def cell1145 : CellCertificate where
  tauBall := tau1145
  contactCenter := center1145
  contactBall := contact1145
  work := work1145
  center_sq := center_sq1145
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1145.1
  jac_ok := checks1145.2.1
  accepted := checks1145.2.2

def tau1146 : RatBall :=
  ⟨⟨23/160, 49/160⟩, 3/320⟩
def center1146 : GaussianRat :=
  ⟨109172181/1000000000, 42835301/200000000⟩
def contact1146 : RatBall := localContactBall tau1146 center1146
def work1146 : RoundedTauEval :=
  evalTau precision tau1146 contact1146 logTwoBall

theorem center_sq1146 : (center1146.re : ℝ)^2 +
    (center1146.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1146]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1146 : work1146.theta.ok = true ∧
    work1146.jac.invOK = true ∧ acceptsUnitSq work1146.out = true := by decide +kernel

def cell1146 : CellCertificate where
  tauBall := tau1146
  contactCenter := center1146
  contactBall := contact1146
  work := work1146
  center_sq := center_sq1146
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1146.1
  jac_ok := checks1146.2.1
  accepted := checks1146.2.2

def tau1147 : RatBall :=
  ⟨⟨21/160, 51/160⟩, 3/320⟩
def center1147 : GaussianRat :=
  ⟨100729897/1000000000, 44886561/200000000⟩
def contact1147 : RatBall := localContactBall tau1147 center1147
def work1147 : RoundedTauEval :=
  evalTau precision tau1147 contact1147 logTwoBall

theorem center_sq1147 : (center1147.re : ℝ)^2 +
    (center1147.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1147]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1147 : work1147.theta.ok = true ∧
    work1147.jac.invOK = true ∧ acceptsUnitSq work1147.out = true := by decide +kernel

def cell1147 : CellCertificate where
  tauBall := tau1147
  contactCenter := center1147
  contactBall := contact1147
  work := work1147
  center_sq := center_sq1147
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1147.1
  jac_ok := checks1147.2.1
  accepted := checks1147.2.2

def tau1148 : RatBall :=
  ⟨⟨17/160, 53/160⟩, 3/320⟩
def center1148 : GaussianRat :=
  ⟨82567747/1000000000, 117805603/500000000⟩
def contact1148 : RatBall := localContactBall tau1148 center1148
def work1148 : RoundedTauEval :=
  evalTau precision tau1148 contact1148 logTwoBall

theorem center_sq1148 : (center1148.re : ℝ)^2 +
    (center1148.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1148]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1148 : work1148.theta.ok = true ∧
    work1148.jac.invOK = true ∧ acceptsUnitSq work1148.out = true := by decide +kernel

def cell1148 : CellCertificate where
  tauBall := tau1148
  contactCenter := center1148
  contactBall := contact1148
  work := work1148
  center_sq := center_sq1148
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1148.1
  jac_ok := checks1148.2.1
  accepted := checks1148.2.2

def tau1149 : RatBall :=
  ⟨⟨5/32, 49/160⟩, 3/320⟩
def center1149 : GaussianRat :=
  ⟨23686489/200000000, 53305887/250000000⟩
def contact1149 : RatBall := localContactBall tau1149 center1149
def work1149 : RoundedTauEval :=
  evalTau precision tau1149 contact1149 logTwoBall

theorem center_sq1149 : (center1149.re : ℝ)^2 +
    (center1149.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1149]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1149 : work1149.theta.ok = true ∧
    work1149.jac.invOK = true ∧ acceptsUnitSq work1149.out = true := by decide +kernel

def cell1149 : CellCertificate where
  tauBall := tau1149
  contactCenter := center1149
  contactBall := contact1149
  work := work1149
  center_sq := center_sq1149
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1149.1
  jac_ok := checks1149.2.1
  accepted := checks1149.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143


