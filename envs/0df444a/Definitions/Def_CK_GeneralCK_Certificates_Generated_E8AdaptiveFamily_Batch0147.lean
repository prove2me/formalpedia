-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0147
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0147
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:02:56.213102+00:00
-- url     : https://prove2.me/theorems/7caf218e-9a9f-475b-8a3e-99e9ad32fa1c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0147` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0147` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0147` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0147 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0147.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0147 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0147

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1176 : RatBall :=
  ⟨⟨43/160, 37/160⟩, 3/320⟩
def center1176 : GaussianRat :=
  ⟨191209303/1000000000, 1887097/12500000⟩
def contact1176 : RatBall := localContactBall tau1176 center1176
def work1176 : RoundedTauEval :=
  evalTau precision tau1176 contact1176 logTwoBall

theorem center_sq1176 : (center1176.re : ℝ)^2 +
    (center1176.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1176]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1176 : work1176.theta.ok = true ∧
    work1176.jac.invOK = true ∧ acceptsUnitSq work1176.out = true := by decide +kernel

def cell1176 : CellCertificate where
  tauBall := tau1176
  contactCenter := center1176
  contactBall := contact1176
  work := work1176
  center_sq := center_sq1176
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1176.1
  jac_ok := checks1176.2.1
  accepted := checks1176.2.2

def tau1177 : RatBall :=
  ⟨⟨41/160, 39/160⟩, 3/320⟩
def center1177 : GaussianRat :=
  ⟨91934683/500000000, 80231659/500000000⟩
def contact1177 : RatBall := localContactBall tau1177 center1177
def work1177 : RoundedTauEval :=
  evalTau precision tau1177 contact1177 logTwoBall

theorem center_sq1177 : (center1177.re : ℝ)^2 +
    (center1177.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1177]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1177 : work1177.theta.ok = true ∧
    work1177.jac.invOK = true ∧ acceptsUnitSq work1177.out = true := by decide +kernel

def cell1177 : CellCertificate where
  tauBall := tau1177
  contactCenter := center1177
  contactBall := contact1177
  work := work1177
  center_sq := center_sq1177
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1177.1
  jac_ok := checks1177.2.1
  accepted := checks1177.2.2

def tau1178 : RatBall :=
  ⟨⟨43/160, 39/160⟩, 3/320⟩
def center1178 : GaussianRat :=
  ⟨96152483/500000000, 159351351/1000000000⟩
def contact1178 : RatBall := localContactBall tau1178 center1178
def work1178 : RoundedTauEval :=
  evalTau precision tau1178 contact1178 logTwoBall

theorem center_sq1178 : (center1178.re : ℝ)^2 +
    (center1178.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1178]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1178 : work1178.theta.ok = true ∧
    work1178.jac.invOK = true ∧ acceptsUnitSq work1178.out = true := by decide +kernel

def cell1178 : CellCertificate where
  tauBall := tau1178
  contactCenter := center1178
  contactBall := contact1178
  work := work1178
  center_sq := center_sq1178
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1178.1
  jac_ok := checks1178.2.1
  accepted := checks1178.2.2

def tau1179 : RatBall :=
  ⟨⟨9/32, 37/160⟩, 3/320⟩
def center1179 : GaussianRat :=
  ⟨199541503/1000000000, 74944839/500000000⟩
def contact1179 : RatBall := localContactBall tau1179 center1179
def work1179 : RoundedTauEval :=
  evalTau precision tau1179 contact1179 logTwoBall

theorem center_sq1179 : (center1179.re : ℝ)^2 +
    (center1179.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1179]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1179 : work1179.theta.ok = true ∧
    work1179.jac.invOK = true ∧ acceptsUnitSq work1179.out = true := by decide +kernel

def cell1179 : CellCertificate where
  tauBall := tau1179
  contactCenter := center1179
  contactBall := contact1179
  work := work1179
  center_sq := center_sq1179
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1179.1
  jac_ok := checks1179.2.1
  accepted := checks1179.2.2

def tau1180 : RatBall :=
  ⟨⟨47/160, 37/160⟩, 3/320⟩
def center1180 : GaussianRat :=
  ⟨103902067/500000000, 37194907/250000000⟩
def contact1180 : RatBall := localContactBall tau1180 center1180
def work1180 : RoundedTauEval :=
  evalTau precision tau1180 contact1180 logTwoBall

theorem center_sq1180 : (center1180.re : ℝ)^2 +
    (center1180.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1180]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1180 : work1180.theta.ok = true ∧
    work1180.jac.invOK = true ∧ acceptsUnitSq work1180.out = true := by decide +kernel

def cell1180 : CellCertificate where
  tauBall := tau1180
  contactCenter := center1180
  contactBall := contact1180
  work := work1180
  center_sq := center_sq1180
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1180.1
  jac_ok := checks1180.2.1
  accepted := checks1180.2.2

def tau1181 : RatBall :=
  ⟨⟨9/32, 39/160⟩, 3/320⟩
def center1181 : GaussianRat :=
  ⟨200670971/1000000000, 79101837/500000000⟩
def contact1181 : RatBall := localContactBall tau1181 center1181
def work1181 : RoundedTauEval :=
  evalTau precision tau1181 contact1181 logTwoBall

theorem center_sq1181 : (center1181.re : ℝ)^2 +
    (center1181.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1181]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1181 : work1181.theta.ok = true ∧
    work1181.jac.invOK = true ∧ acceptsUnitSq work1181.out = true := by decide +kernel

def cell1181 : CellCertificate where
  tauBall := tau1181
  contactCenter := center1181
  contactBall := contact1181
  work := work1181
  center_sq := center_sq1181
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1181.1
  jac_ok := checks1181.2.1
  accepted := checks1181.2.2

def tau1182 : RatBall :=
  ⟨⟨33/160, 41/160⟩, 3/320⟩
def center1182 : GaussianRat :=
  ⟨150430267/1000000000, 1082879/6250000⟩
def contact1182 : RatBall := localContactBall tau1182 center1182
def work1182 : RoundedTauEval :=
  evalTau precision tau1182 contact1182 logTwoBall

theorem center_sq1182 : (center1182.re : ℝ)^2 +
    (center1182.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1182]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1182 : work1182.theta.ok = true ∧
    work1182.jac.invOK = true ∧ acceptsUnitSq work1182.out = true := by decide +kernel

def cell1182 : CellCertificate where
  tauBall := tau1182
  contactCenter := center1182
  contactBall := contact1182
  work := work1182
  center_sq := center_sq1182
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1182.1
  jac_ok := checks1182.2.1
  accepted := checks1182.2.2

def tau1183 : RatBall :=
  ⟨⟨7/32, 41/160⟩, 3/320⟩
def center1183 : GaussianRat :=
  ⟨31833667/200000000, 43062577/250000000⟩
def contact1183 : RatBall := localContactBall tau1183 center1183
def work1183 : RoundedTauEval :=
  evalTau precision tau1183 contact1183 logTwoBall

theorem center_sq1183 : (center1183.re : ℝ)^2 +
    (center1183.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1183]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1183 : work1183.theta.ok = true ∧
    work1183.jac.invOK = true ∧ acceptsUnitSq work1183.out = true := by decide +kernel

def cell1183 : CellCertificate where
  tauBall := tau1183
  contactCenter := center1183
  contactBall := contact1183
  work := work1183
  center_sq := center_sq1183
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1183.1
  jac_ok := checks1183.2.1
  accepted := checks1183.2.2

def cells : List CellCertificate := [cell1176, cell1177, cell1178, cell1179, cell1180, cell1181, cell1182, cell1183]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0147

end


