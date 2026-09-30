-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0012
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0012
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:39:41.786497+00:00
-- url     : https://prove2.me/theorems/81e622f2-67a4-49f1-9dbb-6de1d161e5d7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0012` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0012` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0012` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0012 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0012.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0012 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0012

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0096 : RatBall :=
  ⟨⟨-5/16, -1/80⟩, 3/160⟩
def center0096 : GaussianRat :=
  ⟨-104858117/500000000, -3932321/500000000⟩
def contact0096 : RatBall := localContactBall tau0096 center0096
def work0096 : RoundedTauEval :=
  evalTau precision tau0096 contact0096 logTwoBall

theorem center_sq0096 : (center0096.re : ℝ)^2 +
    (center0096.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0096]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0096 : work0096.theta.ok = true ∧
    work0096.jac.invOK = true ∧ acceptsUnitSq work0096.out = true := by decide +kernel

def cell0096 : CellCertificate where
  tauBall := tau0096
  contactCenter := center0096
  contactBall := contact0096
  work := work0096
  center_sq := center_sq0096
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0096.1
  jac_ok := checks0096.2.1
  accepted := checks0096.2.2

def tau0097 : RatBall :=
  ⟨⟨-23/80, -7/80⟩, 3/160⟩
def center0097 : GaussianRat :=
  ⟨-195201217/1000000000, -13984569/250000000⟩
def contact0097 : RatBall := localContactBall tau0097 center0097
def work0097 : RoundedTauEval :=
  evalTau precision tau0097 contact0097 logTwoBall

theorem center_sq0097 : (center0097.re : ℝ)^2 +
    (center0097.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0097]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0097 : work0097.theta.ok = true ∧
    work0097.jac.invOK = true ∧ acceptsUnitSq work0097.out = true := by decide +kernel

def cell0097 : CellCertificate where
  tauBall := tau0097
  contactCenter := center0097
  contactBall := contact0097
  work := work0097
  center_sq := center_sq0097
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0097.1
  jac_ok := checks0097.2.1
  accepted := checks0097.2.2

def tau0098 : RatBall :=
  ⟨⟨-21/80, -7/80⟩, 3/160⟩
def center0098 : GaussianRat :=
  ⟨-17905297/100000000, -5669463/100000000⟩
def contact0098 : RatBall := localContactBall tau0098 center0098
def work0098 : RoundedTauEval :=
  evalTau precision tau0098 contact0098 logTwoBall

theorem center_sq0098 : (center0098.re : ℝ)^2 +
    (center0098.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0098]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0098 : work0098.theta.ok = true ∧
    work0098.jac.invOK = true ∧ acceptsUnitSq work0098.out = true := by decide +kernel

def cell0098 : CellCertificate where
  tauBall := tau0098
  contactCenter := center0098
  contactBall := contact0098
  work := work0098
  center_sq := center_sq0098
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0098.1
  jac_ok := checks0098.2.1
  accepted := checks0098.2.2

def tau0099 : RatBall :=
  ⟨⟨-23/80, -1/16⟩, 3/160⟩
def center0099 : GaussianRat :=
  ⟨-194534387/1000000000, -7984577/200000000⟩
def contact0099 : RatBall := localContactBall tau0099 center0099
def work0099 : RoundedTauEval :=
  evalTau precision tau0099 contact0099 logTwoBall

theorem center_sq0099 : (center0099.re : ℝ)^2 +
    (center0099.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0099]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0099 : work0099.theta.ok = true ∧
    work0099.jac.invOK = true ∧ acceptsUnitSq work0099.out = true := by decide +kernel

def cell0099 : CellCertificate where
  tauBall := tau0099
  contactCenter := center0099
  contactBall := contact0099
  work := work0099
  center_sq := center_sq0099
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0099.1
  jac_ok := checks0099.2.1
  accepted := checks0099.2.2

def tau0100 : RatBall :=
  ⟨⟨-21/80, -1/16⟩, 3/160⟩
def center0100 : GaussianRat :=
  ⟨-35685561/200000000, -40459851/1000000000⟩
def contact0100 : RatBall := localContactBall tau0100 center0100
def work0100 : RoundedTauEval :=
  evalTau precision tau0100 contact0100 logTwoBall

theorem center_sq0100 : (center0100.re : ℝ)^2 +
    (center0100.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0100]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0100 : work0100.theta.ok = true ∧
    work0100.jac.invOK = true ∧ acceptsUnitSq work0100.out = true := by decide +kernel

def cell0100 : CellCertificate where
  tauBall := tau0100
  contactCenter := center0100
  contactBall := contact0100
  work := work0100
  center_sq := center_sq0100
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0100.1
  jac_ok := checks0100.2.1
  accepted := checks0100.2.2

def tau0101 : RatBall :=
  ⟨⟨-19/80, -7/80⟩, 3/160⟩
def center0101 : GaussianRat :=
  ⟨-162690477/1000000000, -28700003/500000000⟩
def contact0101 : RatBall := localContactBall tau0101 center0101
def work0101 : RoundedTauEval :=
  evalTau precision tau0101 contact0101 logTwoBall

theorem center_sq0101 : (center0101.re : ℝ)^2 +
    (center0101.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0101]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0101 : work0101.theta.ok = true ∧
    work0101.jac.invOK = true ∧ acceptsUnitSq work0101.out = true := by decide +kernel

def cell0101 : CellCertificate where
  tauBall := tau0101
  contactCenter := center0101
  contactBall := contact0101
  work := work0101
  center_sq := center_sq0101
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0101.1
  jac_ok := checks0101.2.1
  accepted := checks0101.2.2

def tau0102 : RatBall :=
  ⟨⟨-17/80, -7/80⟩, 3/160⟩
def center0102 : GaussianRat :=
  ⟨-146129149/1000000000, -3628117/62500000⟩
def contact0102 : RatBall := localContactBall tau0102 center0102
def work0102 : RoundedTauEval :=
  evalTau precision tau0102 contact0102 logTwoBall

theorem center_sq0102 : (center0102.re : ℝ)^2 +
    (center0102.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0102]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0102 : work0102.theta.ok = true ∧
    work0102.jac.invOK = true ∧ acceptsUnitSq work0102.out = true := by decide +kernel

def cell0102 : CellCertificate where
  tauBall := tau0102
  contactCenter := center0102
  contactBall := contact0102
  work := work0102
  center_sq := center_sq0102
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0102.1
  jac_ok := checks0102.2.1
  accepted := checks0102.2.2

def tau0103 : RatBall :=
  ⟨⟨-19/80, -1/16⟩, 3/160⟩
def center0103 : GaussianRat :=
  ⟨-81055451/500000000, -40960501/1000000000⟩
def contact0103 : RatBall := localContactBall tau0103 center0103
def work0103 : RoundedTauEval :=
  evalTau precision tau0103 contact0103 logTwoBall

theorem center_sq0103 : (center0103.re : ℝ)^2 +
    (center0103.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0103]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0103 : work0103.theta.ok = true ∧
    work0103.jac.invOK = true ∧ acceptsUnitSq work0103.out = true := by decide +kernel

def cell0103 : CellCertificate where
  tauBall := tau0103
  contactCenter := center0103
  contactBall := contact0103
  work := work0103
  center_sq := center_sq0103
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0103.1
  jac_ok := checks0103.2.1
  accepted := checks0103.2.2

def cells : List CellCertificate := [cell0096, cell0097, cell0098, cell0099, cell0100, cell0101, cell0102, cell0103]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0012

end


