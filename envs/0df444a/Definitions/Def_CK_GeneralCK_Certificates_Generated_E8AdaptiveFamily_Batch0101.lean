-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0101
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0101
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:47:58.275035+00:00
-- url     : https://prove2.me/theorems/95703319-67fd-4070-b24c-eb58ed0bb898
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0101` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0101` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0101` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0101 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0101.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0101 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0101

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0808 : RatBall :=
  ⟨⟨-51/160, 21/160⟩, 3/320⟩
def center0808 : GaussianRat :=
  ⟨-216902699/1000000000, 20636751/250000000⟩
def contact0808 : RatBall := localContactBall tau0808 center0808
def work0808 : RoundedTauEval :=
  evalTau precision tau0808 contact0808 logTwoBall

theorem center_sq0808 : (center0808.re : ℝ)^2 +
    (center0808.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0808]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0808 : work0808.theta.ok = true ∧
    work0808.jac.invOK = true ∧ acceptsUnitSq work0808.out = true := by decide +kernel

def cell0808 : CellCertificate where
  tauBall := tau0808
  contactCenter := center0808
  contactBall := contact0808
  work := work0808
  center_sq := center_sq0808
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0808.1
  jac_ok := checks0808.2.1
  accepted := checks0808.2.2

def tau0809 : RatBall :=
  ⟨⟨-49/160, 21/160⟩, 3/320⟩
def center0809 : GaussianRat :=
  ⟨-41791301/200000000, 41587123/500000000⟩
def contact0809 : RatBall := localContactBall tau0809 center0809
def work0809 : RoundedTauEval :=
  evalTau precision tau0809 contact0809 logTwoBall

theorem center_sq0809 : (center0809.re : ℝ)^2 +
    (center0809.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0809]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0809 : work0809.theta.ok = true ∧
    work0809.jac.invOK = true ∧ acceptsUnitSq work0809.out = true := by decide +kernel

def cell0809 : CellCertificate where
  tauBall := tau0809
  contactCenter := center0809
  contactBall := contact0809
  work := work0809
  center_sq := center_sq0809
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0809.1
  jac_ok := checks0809.2.1
  accepted := checks0809.2.2

def tau0810 : RatBall :=
  ⟨⟨-51/160, 23/160⟩, 3/320⟩
def center0810 : GaussianRat :=
  ⟨-6799051/31250000, 90469443/1000000000⟩
def contact0810 : RatBall := localContactBall tau0810 center0810
def work0810 : RoundedTauEval :=
  evalTau precision tau0810 contact0810 logTwoBall

theorem center_sq0810 : (center0810.re : ℝ)^2 +
    (center0810.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0810]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0810 : work0810.theta.ok = true ∧
    work0810.jac.invOK = true ∧ acceptsUnitSq work0810.out = true := by decide +kernel

def cell0810 : CellCertificate where
  tauBall := tau0810
  contactCenter := center0810
  contactBall := contact0810
  work := work0810
  center_sq := center_sq0810
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0810.1
  jac_ok := checks0810.2.1
  accepted := checks0810.2.2

def tau0811 : RatBall :=
  ⟨⟨-49/160, 23/160⟩, 3/320⟩
def center0811 : GaussianRat :=
  ⟨-209607093/1000000000, 22790011/250000000⟩
def contact0811 : RatBall := localContactBall tau0811 center0811
def work0811 : RoundedTauEval :=
  evalTau precision tau0811 contact0811 logTwoBall

theorem center_sq0811 : (center0811.re : ℝ)^2 +
    (center0811.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0811]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0811 : work0811.theta.ok = true ∧
    work0811.jac.invOK = true ∧ acceptsUnitSq work0811.out = true := by decide +kernel

def cell0811 : CellCertificate where
  tauBall := tau0811
  contactCenter := center0811
  contactBall := contact0811
  work := work0811
  center_sq := center_sq0811
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0811.1
  jac_ok := checks0811.2.1
  accepted := checks0811.2.2

def tau0812 : RatBall :=
  ⟨⟨-59/160, 5/32⟩, 3/320⟩
def center0812 : GaussianRat :=
  ⟨-1996423/8000000, 19043899/200000000⟩
def contact0812 : RatBall := localContactBall tau0812 center0812
def work0812 : RoundedTauEval :=
  evalTau precision tau0812 contact0812 logTwoBall

theorem center_sq0812 : (center0812.re : ℝ)^2 +
    (center0812.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0812]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0812 : work0812.theta.ok = true ∧
    work0812.jac.invOK = true ∧ acceptsUnitSq work0812.out = true := by decide +kernel

def cell0812 : CellCertificate where
  tauBall := tau0812
  contactCenter := center0812
  contactBall := contact0812
  work := work0812
  center_sq := center_sq0812
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0812.1
  jac_ok := checks0812.2.1
  accepted := checks0812.2.2

def tau0813 : RatBall :=
  ⟨⟨-57/160, 5/32⟩, 3/320⟩
def center0813 : GaussianRat :=
  ⟨-7557593/31250000, 96039881/1000000000⟩
def contact0813 : RatBall := localContactBall tau0813 center0813
def work0813 : RoundedTauEval :=
  evalTau precision tau0813 contact0813 logTwoBall

theorem center_sq0813 : (center0813.re : ℝ)^2 +
    (center0813.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0813]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0813 : work0813.theta.ok = true ∧
    work0813.jac.invOK = true ∧ acceptsUnitSq work0813.out = true := by decide +kernel

def cell0813 : CellCertificate where
  tauBall := tau0813
  contactCenter := center0813
  contactBall := contact0813
  work := work0813
  center_sq := center_sq0813
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0813.1
  jac_ok := checks0813.2.1
  accepted := checks0813.2.2

def tau0814 : RatBall :=
  ⟨⟨-59/160, 27/160⟩, 3/320⟩
def center0814 : GaussianRat :=
  ⟨-6260393/25000000, 51450627/500000000⟩
def contact0814 : RatBall := localContactBall tau0814 center0814
def work0814 : RoundedTauEval :=
  evalTau precision tau0814 contact0814 logTwoBall

theorem center_sq0814 : (center0814.re : ℝ)^2 +
    (center0814.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0814]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0814 : work0814.theta.ok = true ∧
    work0814.jac.invOK = true ∧ acceptsUnitSq work0814.out = true := by decide +kernel

def cell0814 : CellCertificate where
  tauBall := tau0814
  contactCenter := center0814
  contactBall := contact0814
  work := work0814
  center_sq := center_sq0814
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0814.1
  jac_ok := checks0814.2.1
  accepted := checks0814.2.2

def tau0815 : RatBall :=
  ⟨⟨-57/160, 27/160⟩, 3/320⟩
def center0815 : GaussianRat :=
  ⟨-242691133/1000000000, 103792249/1000000000⟩
def contact0815 : RatBall := localContactBall tau0815 center0815
def work0815 : RoundedTauEval :=
  evalTau precision tau0815 contact0815 logTwoBall

theorem center_sq0815 : (center0815.re : ℝ)^2 +
    (center0815.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0815]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0815 : work0815.theta.ok = true ∧
    work0815.jac.invOK = true ∧ acceptsUnitSq work0815.out = true := by decide +kernel

def cell0815 : CellCertificate where
  tauBall := tau0815
  contactCenter := center0815
  contactBall := contact0815
  work := work0815
  center_sq := center_sq0815
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0815.1
  jac_ok := checks0815.2.1
  accepted := checks0815.2.2

def cells : List CellCertificate := [cell0808, cell0809, cell0810, cell0811, cell0812, cell0813, cell0814, cell0815]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0101

end


