-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0134_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0134_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:18:58.011075+00:00
-- url     : https://prove2.me/theorems/624a967e-71b3-411a-bfca-f826e26d2e23
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0134 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1072 : RatBall :=
  ⟨⟨27/160, 37/160⟩, 3/320⟩
def center1072 : GaussianRat :=
  ⟨122297939/1000000000, 158228017/1000000000⟩
def contact1072 : RatBall := localContactBall tau1072 center1072
def work1072 : RoundedTauEval :=
  evalTau precision tau1072 contact1072 logTwoBall

theorem center_sq1072 : (center1072.re : ℝ)^2 +
    (center1072.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1072]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1072 : work1072.theta.ok = true ∧
    work1072.jac.invOK = true ∧ acceptsUnitSq work1072.out = true := by decide +kernel

def cell1072 : CellCertificate where
  tauBall := tau1072
  contactCenter := center1072
  contactBall := contact1072
  work := work1072
  center_sq := center_sq1072
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1072.1
  jac_ok := checks1072.2.1
  accepted := checks1072.2.2

def tau1073 : RatBall :=
  ⟨⟨5/32, 39/160⟩, 3/320⟩
def center1073 : GaussianRat :=
  ⟨57074691/500000000, 83923163/500000000⟩
def contact1073 : RatBall := localContactBall tau1073 center1073
def work1073 : RoundedTauEval :=
  evalTau precision tau1073 contact1073 logTwoBall

theorem center_sq1073 : (center1073.re : ℝ)^2 +
    (center1073.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1073]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1073 : work1073.theta.ok = true ∧
    work1073.jac.invOK = true ∧ acceptsUnitSq work1073.out = true := by decide +kernel

def cell1073 : CellCertificate where
  tauBall := tau1073
  contactCenter := center1073
  contactBall := contact1073
  work := work1073
  center_sq := center_sq1073
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1073.1
  jac_ok := checks1073.2.1
  accepted := checks1073.2.2

def tau1074 : RatBall :=
  ⟨⟨27/160, 39/160⟩, 3/320⟩
def center1074 : GaussianRat :=
  ⟨123057717/1000000000, 167087407/1000000000⟩
def contact1074 : RatBall := localContactBall tau1074 center1074
def work1074 : RoundedTauEval :=
  evalTau precision tau1074 contact1074 logTwoBall

theorem center_sq1074 : (center1074.re : ℝ)^2 +
    (center1074.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1074]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1074 : work1074.theta.ok = true ∧
    work1074.jac.invOK = true ∧ acceptsUnitSq work1074.out = true := by decide +kernel

def cell1074 : CellCertificate where
  tauBall := tau1074
  contactCenter := center1074
  contactBall := contact1074
  work := work1074
  center_sq := center_sq1074
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1074.1
  jac_ok := checks1074.2.1
  accepted := checks1074.2.2

def tau1075 : RatBall :=
  ⟨⟨29/160, 37/160⟩, 3/320⟩
def center1075 : GaussianRat :=
  ⟨8194291/62500000, 7873457/50000000⟩
def contact1075 : RatBall := localContactBall tau1075 center1075
def work1075 : RoundedTauEval :=
  evalTau precision tau1075 contact1075 logTwoBall

theorem center_sq1075 : (center1075.re : ℝ)^2 +
    (center1075.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1075]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1075 : work1075.theta.ok = true ∧
    work1075.jac.invOK = true ∧ acceptsUnitSq work1075.out = true := by decide +kernel

def cell1075 : CellCertificate where
  tauBall := tau1075
  contactCenter := center1075
  contactBall := contact1075
  work := work1075
  center_sq := center_sq1075
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1075.1
  jac_ok := checks1075.2.1
  accepted := checks1075.2.2

def tau1076 : RatBall :=
  ⟨⟨31/160, 37/160⟩, 3/320⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134


