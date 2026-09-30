-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0072
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0072
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:04:21.291981+00:00
-- url     : https://prove2.me/theorems/9d8e0070-f2dd-4c52-b1d6-92c84d589726
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0072` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0072` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0072` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0072 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0072.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0072 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0072

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0576 : RatBall :=
  ⟨⟨9/160, -53/160⟩, 3/320⟩
def center0576 : GaussianRat :=
  ⟨43918333/1000000000, -238021713/1000000000⟩
def contact0576 : RatBall := localContactBall tau0576 center0576
def work0576 : RoundedTauEval :=
  evalTau precision tau0576 contact0576 logTwoBall

theorem center_sq0576 : (center0576.re : ℝ)^2 +
    (center0576.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0576]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0576 : work0576.theta.ok = true ∧
    work0576.jac.invOK = true ∧ acceptsUnitSq work0576.out = true := by decide +kernel

def cell0576 : CellCertificate where
  tauBall := tau0576
  contactCenter := center0576
  contactBall := contact0576
  work := work0576
  center_sq := center_sq0576
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0576.1
  jac_ok := checks0576.2.1
  accepted := checks0576.2.2

def tau0577 : RatBall :=
  ⟨⟨11/160, -53/160⟩, 3/320⟩
def center0577 : GaussianRat :=
  ⟨53629143/1000000000, -118776899/500000000⟩
def contact0577 : RatBall := localContactBall tau0577 center0577
def work0577 : RoundedTauEval :=
  evalTau precision tau0577 contact0577 logTwoBall

theorem center_sq0577 : (center0577.re : ℝ)^2 +
    (center0577.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0577]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0577 : work0577.theta.ok = true ∧
    work0577.jac.invOK = true ∧ acceptsUnitSq work0577.out = true := by decide +kernel

def cell0577 : CellCertificate where
  tauBall := tau0577
  contactCenter := center0577
  contactBall := contact0577
  work := work0577
  center_sq := center_sq0577
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0577.1
  jac_ok := checks0577.2.1
  accepted := checks0577.2.2

def tau0578 : RatBall :=
  ⟨⟨13/160, -53/160⟩, 3/320⟩
def center0578 : GaussianRat :=
  ⟨63310961/1000000000, -236995059/1000000000⟩
def contact0578 : RatBall := localContactBall tau0578 center0578
def work0578 : RoundedTauEval :=
  evalTau precision tau0578 contact0578 logTwoBall

theorem center_sq0578 : (center0578.re : ℝ)^2 +
    (center0578.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0578]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0578 : work0578.theta.ok = true ∧
    work0578.jac.invOK = true ∧ acceptsUnitSq work0578.out = true := by decide +kernel

def cell0578 : CellCertificate where
  tauBall := tau0578
  contactCenter := center0578
  contactBall := contact0578
  work := work0578
  center_sq := center_sq0578
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0578.1
  jac_ok := checks0578.2.1
  accepted := checks0578.2.2

def tau0579 : RatBall :=
  ⟨⟨3/32, -53/160⟩, 3/320⟩
def center0579 : GaussianRat :=
  ⟨72958787/1000000000, -47269393/200000000⟩
def contact0579 : RatBall := localContactBall tau0579 center0579
def work0579 : RoundedTauEval :=
  evalTau precision tau0579 contact0579 logTwoBall

theorem center_sq0579 : (center0579.re : ℝ)^2 +
    (center0579.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0579]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0579 : work0579.theta.ok = true ∧
    work0579.jac.invOK = true ∧ acceptsUnitSq work0579.out = true := by decide +kernel

def cell0579 : CellCertificate where
  tauBall := tau0579
  contactCenter := center0579
  contactBall := contact0579
  work := work0579
  center_sq := center_sq0579
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0579.1
  jac_ok := checks0579.2.1
  accepted := checks0579.2.2

def tau0580 : RatBall :=
  ⟨⟨9/160, -51/160⟩, 3/320⟩
def center0580 : GaussianRat :=
  ⟨21754011/500000000, -445983/1953125⟩
def contact0580 : RatBall := localContactBall tau0580 center0580
def work0580 : RoundedTauEval :=
  evalTau precision tau0580 contact0580 logTwoBall

theorem center_sq0580 : (center0580.re : ℝ)^2 +
    (center0580.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0580]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0580 : work0580.theta.ok = true ∧
    work0580.jac.invOK = true ∧ acceptsUnitSq work0580.out = true := by decide +kernel

def cell0580 : CellCertificate where
  tauBall := tau0580
  contactCenter := center0580
  contactBall := contact0580
  work := work0580
  center_sq := center_sq0580
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0580.1
  jac_ok := checks0580.2.1
  accepted := checks0580.2.2

def tau0581 : RatBall :=
  ⟨⟨11/160, -51/160⟩, 3/320⟩
def center0581 : GaussianRat :=
  ⟨53129867/1000000000, -56975307/250000000⟩
def contact0581 : RatBall := localContactBall tau0581 center0581
def work0581 : RoundedTauEval :=
  evalTau precision tau0581 contact0581 logTwoBall

theorem center_sq0581 : (center0581.re : ℝ)^2 +
    (center0581.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0581]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0581 : work0581.theta.ok = true ∧
    work0581.jac.invOK = true ∧ acceptsUnitSq work0581.out = true := by decide +kernel

def cell0581 : CellCertificate where
  tauBall := tau0581
  contactCenter := center0581
  contactBall := contact0581
  work := work0581
  center_sq := center_sq0581
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0581.1
  jac_ok := checks0581.2.1
  accepted := checks0581.2.2

def tau0582 : RatBall :=
  ⟨⟨9/160, -49/160⟩, 3/320⟩
def center0582 : GaussianRat :=
  ⟨43120523/1000000000, -109375967/500000000⟩
def contact0582 : RatBall := localContactBall tau0582 center0582
def work0582 : RoundedTauEval :=
  evalTau precision tau0582 contact0582 logTwoBall

theorem center_sq0582 : (center0582.re : ℝ)^2 +
    (center0582.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0582]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0582 : work0582.theta.ok = true ∧
    work0582.jac.invOK = true ∧ acceptsUnitSq work0582.out = true := by decide +kernel

def cell0582 : CellCertificate where
  tauBall := tau0582
  contactCenter := center0582
  contactBall := contact0582
  work := work0582
  center_sq := center_sq0582
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0582.1
  jac_ok := checks0582.2.1
  accepted := checks0582.2.2

def tau0583 : RatBall :=
  ⟨⟨11/160, -49/160⟩, 3/320⟩
def center0583 : GaussianRat :=
  ⟨52658297/1000000000, -109167283/500000000⟩
def contact0583 : RatBall := localContactBall tau0583 center0583
def work0583 : RoundedTauEval :=
  evalTau precision tau0583 contact0583 logTwoBall

theorem center_sq0583 : (center0583.re : ℝ)^2 +
    (center0583.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0583]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0583 : work0583.theta.ok = true ∧
    work0583.jac.invOK = true ∧ acceptsUnitSq work0583.out = true := by decide +kernel

def cell0583 : CellCertificate where
  tauBall := tau0583
  contactCenter := center0583
  contactBall := contact0583
  work := work0583
  center_sq := center_sq0583
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0583.1
  jac_ok := checks0583.2.1
  accepted := checks0583.2.2

def cells : List CellCertificate := [cell0576, cell0577, cell0578, cell0579, cell0580, cell0581, cell0582, cell0583]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0072

end


