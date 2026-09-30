-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0132
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0132
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:49:25.468109+00:00
-- url     : https://prove2.me/theorems/9b650e06-a31c-4d21-875c-bcd4143bba90
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0132` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0132` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0132` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0132 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0132.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0132 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0132

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1056 : RatBall :=
  ⟨⟨53/160, 31/160⟩, 3/320⟩
def center1056 : GaussianRat :=
  ⟨114433899/500000000, 30340451/250000000⟩
def contact1056 : RatBall := localContactBall tau1056 center1056
def work1056 : RoundedTauEval :=
  evalTau precision tau1056 contact1056 logTwoBall

theorem center_sq1056 : (center1056.re : ℝ)^2 +
    (center1056.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1056]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1056 : work1056.theta.ok = true ∧
    work1056.jac.invOK = true ∧ acceptsUnitSq work1056.out = true := by decide +kernel

def cell1056 : CellCertificate where
  tauBall := tau1056
  contactCenter := center1056
  contactBall := contact1056
  work := work1056
  center_sq := center_sq1056
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1056.1
  jac_ok := checks1056.2.1
  accepted := checks1056.2.2

def tau1057 : RatBall :=
  ⟨⟨11/32, 31/160⟩, 3/320⟩
def center1057 : GaussianRat :=
  ⟨47354053/200000000, 30090849/250000000⟩
def contact1057 : RatBall := localContactBall tau1057 center1057
def work1057 : RoundedTauEval :=
  evalTau precision tau1057 contact1057 logTwoBall

theorem center_sq1057 : (center1057.re : ℝ)^2 +
    (center1057.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1057]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1057 : work1057.theta.ok = true ∧
    work1057.jac.invOK = true ∧ acceptsUnitSq work1057.out = true := by decide +kernel

def cell1057 : CellCertificate where
  tauBall := tau1057
  contactCenter := center1057
  contactBall := contact1057
  work := work1057
  center_sq := center_sq1057
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1057.1
  jac_ok := checks1057.2.1
  accepted := checks1057.2.2

def tau1058 : RatBall :=
  ⟨⟨57/160, 5/32⟩, 3/320⟩
def center1058 : GaussianRat :=
  ⟨7557593/31250000, 96039881/1000000000⟩
def contact1058 : RatBall := localContactBall tau1058 center1058
def work1058 : RoundedTauEval :=
  evalTau precision tau1058 contact1058 logTwoBall

theorem center_sq1058 : (center1058.re : ℝ)^2 +
    (center1058.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1058]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1058 : work1058.theta.ok = true ∧
    work1058.jac.invOK = true ∧ acceptsUnitSq work1058.out = true := by decide +kernel

def cell1058 : CellCertificate where
  tauBall := tau1058
  contactCenter := center1058
  contactBall := contact1058
  work := work1058
  center_sq := center_sq1058
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1058.1
  jac_ok := checks1058.2.1
  accepted := checks1058.2.2

def tau1059 : RatBall :=
  ⟨⟨59/160, 5/32⟩, 3/320⟩
def center1059 : GaussianRat :=
  ⟨1996423/8000000, 19043899/200000000⟩
def contact1059 : RatBall := localContactBall tau1059 center1059
def work1059 : RoundedTauEval :=
  evalTau precision tau1059 contact1059 logTwoBall

theorem center_sq1059 : (center1059.re : ℝ)^2 +
    (center1059.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1059]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1059 : work1059.theta.ok = true ∧
    work1059.jac.invOK = true ∧ acceptsUnitSq work1059.out = true := by decide +kernel

def cell1059 : CellCertificate where
  tauBall := tau1059
  contactCenter := center1059
  contactBall := contact1059
  work := work1059
  center_sq := center_sq1059
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1059.1
  jac_ok := checks1059.2.1
  accepted := checks1059.2.2

def tau1060 : RatBall :=
  ⟨⟨57/160, 27/160⟩, 3/320⟩
def center1060 : GaussianRat :=
  ⟨242691133/1000000000, 103792249/1000000000⟩
def contact1060 : RatBall := localContactBall tau1060 center1060
def work1060 : RoundedTauEval :=
  evalTau precision tau1060 contact1060 logTwoBall

theorem center_sq1060 : (center1060.re : ℝ)^2 +
    (center1060.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1060]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1060 : work1060.theta.ok = true ∧
    work1060.jac.invOK = true ∧ acceptsUnitSq work1060.out = true := by decide +kernel

def cell1060 : CellCertificate where
  tauBall := tau1060
  contactCenter := center1060
  contactBall := contact1060
  work := work1060
  center_sq := center_sq1060
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1060.1
  jac_ok := checks1060.2.1
  accepted := checks1060.2.2

def tau1061 : RatBall :=
  ⟨⟨59/160, 27/160⟩, 3/320⟩
def center1061 : GaussianRat :=
  ⟨6260393/25000000, 51450627/500000000⟩
def contact1061 : RatBall := localContactBall tau1061 center1061
def work1061 : RoundedTauEval :=
  evalTau precision tau1061 contact1061 logTwoBall

theorem center_sq1061 : (center1061.re : ℝ)^2 +
    (center1061.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1061]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1061 : work1061.theta.ok = true ∧
    work1061.jac.invOK = true ∧ acceptsUnitSq work1061.out = true := by decide +kernel

def cell1061 : CellCertificate where
  tauBall := tau1061
  contactCenter := center1061
  contactBall := contact1061
  work := work1061
  center_sq := center_sq1061
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1061.1
  jac_ok := checks1061.2.1
  accepted := checks1061.2.2

def tau1062 : RatBall :=
  ⟨⟨57/160, 29/160⟩, 3/320⟩
def center1062 : GaussianRat :=
  ⟨243609941/1000000000, 22312087/200000000⟩
def contact1062 : RatBall := localContactBall tau1062 center1062
def work1062 : RoundedTauEval :=
  evalTau precision tau1062 contact1062 logTwoBall

theorem center_sq1062 : (center1062.re : ℝ)^2 +
    (center1062.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1062]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1062 : work1062.theta.ok = true ∧
    work1062.jac.invOK = true ∧ acceptsUnitSq work1062.out = true := by decide +kernel

def cell1062 : CellCertificate where
  tauBall := tau1062
  contactCenter := center1062
  contactBall := contact1062
  work := work1062
  center_sq := center_sq1062
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1062.1
  jac_ok := checks1062.2.1
  accepted := checks1062.2.2

def tau1063 : RatBall :=
  ⟨⟨9/160, 9/32⟩, 3/320⟩
def center1063 : GaussianRat :=
  ⟨21205027/500000000, 199811247/1000000000⟩
def contact1063 : RatBall := localContactBall tau1063 center1063
def work1063 : RoundedTauEval :=
  evalTau precision tau1063 contact1063 logTwoBall

theorem center_sq1063 : (center1063.re : ℝ)^2 +
    (center1063.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1063]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1063 : work1063.theta.ok = true ∧
    work1063.jac.invOK = true ∧ acceptsUnitSq work1063.out = true := by decide +kernel

def cell1063 : CellCertificate where
  tauBall := tau1063
  contactCenter := center1063
  contactBall := contact1063
  work := work1063
  center_sq := center_sq1063
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1063.1
  jac_ok := checks1063.2.1
  accepted := checks1063.2.2

def cells : List CellCertificate := [cell1056, cell1057, cell1058, cell1059, cell1060, cell1061, cell1062, cell1063]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0132

end


