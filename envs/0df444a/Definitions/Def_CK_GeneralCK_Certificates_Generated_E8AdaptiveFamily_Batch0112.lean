-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0112
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0112
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:21:07.474926+00:00
-- url     : https://prove2.me/theorems/e04d56c2-5b1b-4374-857b-b11b77a7c7a9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0112` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0112` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0112` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0112 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0112.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0112 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0112

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0896 : RatBall :=
  ⟨⟨-7/32, 9/32⟩, 3/320⟩
def center0896 : GaussianRat :=
  ⟨-32272717/200000000, 189759799/1000000000⟩
def contact0896 : RatBall := localContactBall tau0896 center0896
def work0896 : RoundedTauEval :=
  evalTau precision tau0896 contact0896 logTwoBall

theorem center_sq0896 : (center0896.re : ℝ)^2 +
    (center0896.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0896]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0896 : work0896.theta.ok = true ∧
    work0896.jac.invOK = true ∧ acceptsUnitSq work0896.out = true := by decide +kernel

def cell0896 : CellCertificate where
  tauBall := tau0896
  contactCenter := center0896
  contactBall := contact0896
  work := work0896
  center_sq := center_sq0896
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0896.1
  jac_ok := checks0896.2.1
  accepted := checks0896.2.2

def tau0897 : RatBall :=
  ⟨⟨-33/160, 9/32⟩, 3/320⟩
def center0897 : GaussianRat :=
  ⟨-9532907/62500000, 95448491/500000000⟩
def contact0897 : RatBall := localContactBall tau0897 center0897
def work0897 : RoundedTauEval :=
  evalTau precision tau0897 contact0897 logTwoBall

theorem center_sq0897 : (center0897.re : ℝ)^2 +
    (center0897.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0897]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0897 : work0897.theta.ok = true ∧
    work0897.jac.invOK = true ∧ acceptsUnitSq work0897.out = true := by decide +kernel

def cell0897 : CellCertificate where
  tauBall := tau0897
  contactCenter := center0897
  contactBall := contact0897
  work := work0897
  center_sq := center_sq0897
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0897.1
  jac_ok := checks0897.2.1
  accepted := checks0897.2.2

def tau0898 : RatBall :=
  ⟨⟨-31/160, 37/160⟩, 3/320⟩
def center0898 : GaussianRat :=
  ⟨-139868391/1000000000, 78332251/500000000⟩
def contact0898 : RatBall := localContactBall tau0898 center0898
def work0898 : RoundedTauEval :=
  evalTau precision tau0898 contact0898 logTwoBall

theorem center_sq0898 : (center0898.re : ℝ)^2 +
    (center0898.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0898]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0898 : work0898.theta.ok = true ∧
    work0898.jac.invOK = true ∧ acceptsUnitSq work0898.out = true := by decide +kernel

def cell0898 : CellCertificate where
  tauBall := tau0898
  contactCenter := center0898
  contactBall := contact0898
  work := work0898
  center_sq := center_sq0898
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0898.1
  jac_ok := checks0898.2.1
  accepted := checks0898.2.2

def tau0899 : RatBall :=
  ⟨⟨-29/160, 37/160⟩, 3/320⟩
def center0899 : GaussianRat :=
  ⟨-8194291/62500000, 7873457/50000000⟩
def contact0899 : RatBall := localContactBall tau0899 center0899
def work0899 : RoundedTauEval :=
  evalTau precision tau0899 contact0899 logTwoBall

theorem center_sq0899 : (center0899.re : ℝ)^2 +
    (center0899.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0899]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0899 : work0899.theta.ok = true ∧
    work0899.jac.invOK = true ∧ acceptsUnitSq work0899.out = true := by decide +kernel

def cell0899 : CellCertificate where
  tauBall := tau0899
  contactCenter := center0899
  contactBall := contact0899
  work := work0899
  center_sq := center_sq0899
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0899.1
  jac_ok := checks0899.2.1
  accepted := checks0899.2.2

def tau0900 : RatBall :=
  ⟨⟨-31/160, 39/160⟩, 3/320⟩
def center0900 : GaussianRat :=
  ⟨-2814451/20000000, 33084071/200000000⟩
def contact0900 : RatBall := localContactBall tau0900 center0900
def work0900 : RoundedTauEval :=
  evalTau precision tau0900 contact0900 logTwoBall

theorem center_sq0900 : (center0900.re : ℝ)^2 +
    (center0900.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0900]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0900 : work0900.theta.ok = true ∧
    work0900.jac.invOK = true ∧ acceptsUnitSq work0900.out = true := by decide +kernel

def cell0900 : CellCertificate where
  tauBall := tau0900
  contactCenter := center0900
  contactBall := contact0900
  work := work0900
  center_sq := center_sq0900
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0900.1
  jac_ok := checks0900.2.1
  accepted := checks0900.2.2

def tau0901 : RatBall :=
  ⟨⟨-29/160, 39/160⟩, 3/320⟩
def center0901 : GaussianRat :=
  ⟨-131916433/1000000000, 83139101/500000000⟩
def contact0901 : RatBall := localContactBall tau0901 center0901
def work0901 : RoundedTauEval :=
  evalTau precision tau0901 contact0901 logTwoBall

theorem center_sq0901 : (center0901.re : ℝ)^2 +
    (center0901.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0901]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0901 : work0901.theta.ok = true ∧
    work0901.jac.invOK = true ∧ acceptsUnitSq work0901.out = true := by decide +kernel

def cell0901 : CellCertificate where
  tauBall := tau0901
  contactCenter := center0901
  contactBall := contact0901
  work := work0901
  center_sq := center_sq0901
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0901.1
  jac_ok := checks0901.2.1
  accepted := checks0901.2.2

def tau0902 : RatBall :=
  ⟨⟨-27/160, 37/160⟩, 3/320⟩
def center0902 : GaussianRat :=
  ⟨-122297939/1000000000, 158228017/1000000000⟩
def contact0902 : RatBall := localContactBall tau0902 center0902
def work0902 : RoundedTauEval :=
  evalTau precision tau0902 contact0902 logTwoBall

theorem center_sq0902 : (center0902.re : ℝ)^2 +
    (center0902.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0902]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0902 : work0902.theta.ok = true ∧
    work0902.jac.invOK = true ∧ acceptsUnitSq work0902.out = true := by decide +kernel

def cell0902 : CellCertificate where
  tauBall := tau0902
  contactCenter := center0902
  contactBall := contact0902
  work := work0902
  center_sq := center_sq0902
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0902.1
  jac_ok := checks0902.2.1
  accepted := checks0902.2.2

def tau0903 : RatBall :=
  ⟨⟨-5/32, 37/160⟩, 3/320⟩
def center0903 : GaussianRat :=
  ⟨-113439149/1000000000, 158939613/1000000000⟩
def contact0903 : RatBall := localContactBall tau0903 center0903
def work0903 : RoundedTauEval :=
  evalTau precision tau0903 contact0903 logTwoBall

theorem center_sq0903 : (center0903.re : ℝ)^2 +
    (center0903.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0903]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0903 : work0903.theta.ok = true ∧
    work0903.jac.invOK = true ∧ acceptsUnitSq work0903.out = true := by decide +kernel

def cell0903 : CellCertificate where
  tauBall := tau0903
  contactCenter := center0903
  contactBall := contact0903
  work := work0903
  center_sq := center_sq0903
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0903.1
  jac_ok := checks0903.2.1
  accepted := checks0903.2.2

def cells : List CellCertificate := [cell0896, cell0897, cell0898, cell0899, cell0900, cell0901, cell0902, cell0903]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0112

end


