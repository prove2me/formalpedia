-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0122
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0122
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:40:06.369044+00:00
-- url     : https://prove2.me/theorems/f6cff6be-fec2-4639-91e1-0079cd547b0d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0122` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0122` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0122` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0122 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0122.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0122 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0122

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0976 : RatBall :=
  ⟨⟨-1/160, 51/160⟩, 3/320⟩
def center0976 : GaussianRat :=
  ⟨-4842747/1000000000, 45846653/200000000⟩
def contact0976 : RatBall := localContactBall tau0976 center0976
def work0976 : RoundedTauEval :=
  evalTau precision tau0976 contact0976 logTwoBall

theorem center_sq0976 : (center0976.re : ℝ)^2 +
    (center0976.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0976]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0976 : work0976.theta.ok = true ∧
    work0976.jac.invOK = true ∧ acceptsUnitSq work0976.out = true := by decide +kernel

def cell0976 : CellCertificate where
  tauBall := tau0976
  contactCenter := center0976
  contactBall := contact0976
  work := work0976
  center_sq := center_sq0976
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0976.1
  jac_ok := checks0976.2.1
  accepted := checks0976.2.2

def tau0977 : RatBall :=
  ⟨⟨-7/160, 53/160⟩, 3/320⟩
def center0977 : GaussianRat :=
  ⟨-17091823/500000000, 119198781/500000000⟩
def contact0977 : RatBall := localContactBall tau0977 center0977
def work0977 : RoundedTauEval :=
  evalTau precision tau0977 contact0977 logTwoBall

theorem center_sq0977 : (center0977.re : ℝ)^2 +
    (center0977.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0977]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0977 : work0977.theta.ok = true ∧
    work0977.jac.invOK = true ∧ acceptsUnitSq work0977.out = true := by decide +kernel

def cell0977 : CellCertificate where
  tauBall := tau0977
  contactCenter := center0977
  contactBall := contact0977
  work := work0977
  center_sq := center_sq0977
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0977.1
  jac_ok := checks0977.2.1
  accepted := checks0977.2.2

def tau0978 : RatBall :=
  ⟨⟨-1/32, 53/160⟩, 3/320⟩
def center0978 : GaussianRat :=
  ⟨-2443029/100000000, 119340169/500000000⟩
def contact0978 : RatBall := localContactBall tau0978 center0978
def work0978 : RoundedTauEval :=
  evalTau precision tau0978 contact0978 logTwoBall

theorem center_sq0978 : (center0978.re : ℝ)^2 +
    (center0978.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0978]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0978 : work0978.theta.ok = true ∧
    work0978.jac.invOK = true ∧ acceptsUnitSq work0978.out = true := by decide +kernel

def cell0978 : CellCertificate where
  tauBall := tau0978
  contactCenter := center0978
  contactBall := contact0978
  work := work0978
  center_sq := center_sq0978
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0978.1
  jac_ok := checks0978.2.1
  accepted := checks0978.2.2

def tau0979 : RatBall :=
  ⟨⟨-7/160, 11/32⟩, 3/320⟩
def center0979 : GaussianRat :=
  ⟨-6904519/200000000, 248189889/1000000000⟩
def contact0979 : RatBall := localContactBall tau0979 center0979
def work0979 : RoundedTauEval :=
  evalTau precision tau0979 contact0979 logTwoBall

theorem center_sq0979 : (center0979.re : ℝ)^2 +
    (center0979.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0979]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0979 : work0979.theta.ok = true ∧
    work0979.jac.invOK = true ∧ acceptsUnitSq work0979.out = true := by decide +kernel

def cell0979 : CellCertificate where
  tauBall := tau0979
  contactCenter := center0979
  contactBall := contact0979
  work := work0979
  center_sq := center_sq0979
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0979.1
  jac_ok := checks0979.2.1
  accepted := checks0979.2.2

def tau0980 : RatBall :=
  ⟨⟨-1/32, 11/32⟩, 3/320⟩
def center0980 : GaussianRat :=
  ⟨-24673061/1000000000, 248489097/1000000000⟩
def contact0980 : RatBall := localContactBall tau0980 center0980
def work0980 : RoundedTauEval :=
  evalTau precision tau0980 contact0980 logTwoBall

theorem center_sq0980 : (center0980.re : ℝ)^2 +
    (center0980.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0980]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0980 : work0980.theta.ok = true ∧
    work0980.jac.invOK = true ∧ acceptsUnitSq work0980.out = true := by decide +kernel

def cell0980 : CellCertificate where
  tauBall := tau0980
  contactCenter := center0980
  contactBall := contact0980
  work := work0980
  center_sq := center_sq0980
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0980.1
  jac_ok := checks0980.2.1
  accepted := checks0980.2.2

def tau0981 : RatBall :=
  ⟨⟨-3/160, 53/160⟩, 3/320⟩
def center0981 : GaussianRat :=
  ⟨-1832943/125000000, 238869281/1000000000⟩
def contact0981 : RatBall := localContactBall tau0981 center0981
def work0981 : RoundedTauEval :=
  evalTau precision tau0981 contact0981 logTwoBall

theorem center_sq0981 : (center0981.re : ℝ)^2 +
    (center0981.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0981]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0981 : work0981.theta.ok = true ∧
    work0981.jac.invOK = true ∧ acceptsUnitSq work0981.out = true := by decide +kernel

def cell0981 : CellCertificate where
  tauBall := tau0981
  contactCenter := center0981
  contactBall := contact0981
  work := work0981
  center_sq := center_sq0981
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0981.1
  jac_ok := checks0981.2.1
  accepted := checks0981.2.2

def tau0982 : RatBall :=
  ⟨⟨-1/160, 53/160⟩, 3/320⟩
def center0982 : GaussianRat :=
  ⟨-611093/125000000, 238963881/1000000000⟩
def contact0982 : RatBall := localContactBall tau0982 center0982
def work0982 : RoundedTauEval :=
  evalTau precision tau0982 contact0982 logTwoBall

theorem center_sq0982 : (center0982.re : ℝ)^2 +
    (center0982.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0982]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0982 : work0982.theta.ok = true ∧
    work0982.jac.invOK = true ∧ acceptsUnitSq work0982.out = true := by decide +kernel

def cell0982 : CellCertificate where
  tauBall := tau0982
  contactCenter := center0982
  contactBall := contact0982
  work := work0982
  center_sq := center_sq0982
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0982.1
  jac_ok := checks0982.2.1
  accepted := checks0982.2.2

def tau0983 : RatBall :=
  ⟨⟨-3/160, 11/32⟩, 3/320⟩
def center0983 : GaussianRat :=
  ⟨-7404737/500000000, 31086129/125000000⟩
def contact0983 : RatBall := localContactBall tau0983 center0983
def work0983 : RoundedTauEval :=
  evalTau precision tau0983 contact0983 logTwoBall

theorem center_sq0983 : (center0983.re : ℝ)^2 +
    (center0983.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0983]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0983 : work0983.theta.ok = true ∧
    work0983.jac.invOK = true ∧ acceptsUnitSq work0983.out = true := by decide +kernel

def cell0983 : CellCertificate where
  tauBall := tau0983
  contactCenter := center0983
  contactBall := contact0983
  work := work0983
  center_sq := center_sq0983
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0983.1
  jac_ok := checks0983.2.1
  accepted := checks0983.2.2

def cells : List CellCertificate := [cell0976, cell0977, cell0978, cell0979, cell0980, cell0981, cell0982, cell0983]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0122

end


