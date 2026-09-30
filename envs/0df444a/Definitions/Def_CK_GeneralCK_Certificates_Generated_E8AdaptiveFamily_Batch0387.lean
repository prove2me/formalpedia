-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0387
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0387
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:51:37.295988+00:00
-- url     : https://prove2.me/theorems/41c57f3d-dc93-4009-b8c5-a852ccc772ac
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0387` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0387` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0387` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0387 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0387.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0387 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0387

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3096 : RatBall :=
  ⟨⟨79/640, -237/640⟩, 3/1280⟩
def center3096 : GaussianRat :=
  ⟨98760267/1000000000, -132324589/500000000⟩
def contact3096 : RatBall := localContactBall tau3096 center3096
def work3096 : RoundedTauEval :=
  evalTau precision tau3096 contact3096 logTwoBall

theorem center_sq3096 : (center3096.re : ℝ)^2 +
    (center3096.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3096]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3096 : work3096.theta.ok = true ∧
    work3096.jac.invOK = true ∧ acceptsUnitSq work3096.out = true := by decide +kernel

def cell3096 : CellCertificate where
  tauBall := tau3096
  contactCenter := center3096
  contactBall := contact3096
  work := work3096
  center_sq := center_sq3096
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3096.1
  jac_ok := checks3096.2.1
  accepted := checks3096.2.2

def tau3097 : RatBall :=
  ⟨⟨81/640, -239/640⟩, 3/1280⟩
def center3097 : GaussianRat :=
  ⟨50741661/500000000, -53366229/200000000⟩
def contact3097 : RatBall := localContactBall tau3097 center3097
def work3097 : RoundedTauEval :=
  evalTau precision tau3097 contact3097 logTwoBall

theorem center_sq3097 : (center3097.re : ℝ)^2 +
    (center3097.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3097]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3097 : work3097.theta.ok = true ∧
    work3097.jac.invOK = true ∧ acceptsUnitSq work3097.out = true := by decide +kernel

def cell3097 : CellCertificate where
  tauBall := tau3097
  contactCenter := center3097
  contactBall := contact3097
  work := work3097
  center_sq := center_sq3097
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3097.1
  jac_ok := checks3097.2.1
  accepted := checks3097.2.2

def tau3098 : RatBall :=
  ⟨⟨83/640, -239/640⟩, 3/1280⟩
def center3098 : GaussianRat :=
  ⟨103935163/1000000000, -66638159/250000000⟩
def contact3098 : RatBall := localContactBall tau3098 center3098
def work3098 : RoundedTauEval :=
  evalTau precision tau3098 contact3098 logTwoBall

theorem center_sq3098 : (center3098.re : ℝ)^2 +
    (center3098.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3098]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3098 : work3098.theta.ok = true ∧
    work3098.jac.invOK = true ∧ acceptsUnitSq work3098.out = true := by decide +kernel

def cell3098 : CellCertificate where
  tauBall := tau3098
  contactCenter := center3098
  contactBall := contact3098
  work := work3098
  center_sq := center_sq3098
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3098.1
  jac_ok := checks3098.2.1
  accepted := checks3098.2.2

def tau3099 : RatBall :=
  ⟨⟨81/640, -237/640⟩, 3/1280⟩
def center3099 : GaussianRat :=
  ⟨101209731/1000000000, -10575219/40000000⟩
def contact3099 : RatBall := localContactBall tau3099 center3099
def work3099 : RoundedTauEval :=
  evalTau precision tau3099 contact3099 logTwoBall

theorem center_sq3099 : (center3099.re : ℝ)^2 +
    (center3099.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3099]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3099 : work3099.theta.ok = true ∧
    work3099.jac.invOK = true ∧ acceptsUnitSq work3099.out = true := by decide +kernel

def cell3099 : CellCertificate where
  tauBall := tau3099
  contactCenter := center3099
  contactBall := contact3099
  work := work3099
  center_sq := center_sq3099
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3099.1
  jac_ok := checks3099.2.1
  accepted := checks3099.2.2

def tau3100 : RatBall :=
  ⟨⟨83/640, -237/640⟩, 3/1280⟩
def center3100 : GaussianRat :=
  ⟨6478469/62500000, -132052859/500000000⟩
def contact3100 : RatBall := localContactBall tau3100 center3100
def work3100 : RoundedTauEval :=
  evalTau precision tau3100 contact3100 logTwoBall

theorem center_sq3100 : (center3100.re : ℝ)^2 +
    (center3100.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3100]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3100 : work3100.theta.ok = true ∧
    work3100.jac.invOK = true ∧ acceptsUnitSq work3100.out = true := by decide +kernel

def cell3100 : CellCertificate where
  tauBall := tau3100
  contactCenter := center3100
  contactBall := contact3100
  work := work3100
  center_sq := center_sq3100
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3100.1
  jac_ok := checks3100.2.1
  accepted := checks3100.2.2

def tau3101 : RatBall :=
  ⟨⟨17/128, -239/640⟩, 3/1280⟩
def center3101 : GaussianRat :=
  ⟨10638319/100000000, -266268043/1000000000⟩
def contact3101 : RatBall := localContactBall tau3101 center3101
def work3101 : RoundedTauEval :=
  evalTau precision tau3101 contact3101 logTwoBall

theorem center_sq3101 : (center3101.re : ℝ)^2 +
    (center3101.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3101]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3101 : work3101.theta.ok = true ∧
    work3101.jac.invOK = true ∧ acceptsUnitSq work3101.out = true := by decide +kernel

def cell3101 : CellCertificate where
  tauBall := tau3101
  contactCenter := center3101
  contactBall := contact3101
  work := work3101
  center_sq := center_sq3101
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3101.1
  jac_ok := checks3101.2.1
  accepted := checks3101.2.2

def tau3102 : RatBall :=
  ⟨⟨87/640, -239/640⟩, 3/1280⟩
def center3102 : GaussianRat :=
  ⟨4353093/40000000, -53195483/200000000⟩
def contact3102 : RatBall := localContactBall tau3102 center3102
def work3102 : RoundedTauEval :=
  evalTau precision tau3102 contact3102 logTwoBall

theorem center_sq3102 : (center3102.re : ℝ)^2 +
    (center3102.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3102]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3102 : work3102.theta.ok = true ∧
    work3102.jac.invOK = true ∧ acceptsUnitSq work3102.out = true := by decide +kernel

def cell3102 : CellCertificate where
  tauBall := tau3102
  contactCenter := center3102
  contactBall := contact3102
  work := work3102
  center_sq := center_sq3102
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3102.1
  jac_ok := checks3102.2.1
  accepted := checks3102.2.2

def tau3103 : RatBall :=
  ⟨⟨17/128, -237/640⟩, 3/1280⟩
def center3103 : GaussianRat :=
  ⟨106097509/1000000000, -131912477/500000000⟩
def contact3103 : RatBall := localContactBall tau3103 center3103
def work3103 : RoundedTauEval :=
  evalTau precision tau3103 contact3103 logTwoBall

theorem center_sq3103 : (center3103.re : ℝ)^2 +
    (center3103.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3103]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3103 : work3103.theta.ok = true ∧
    work3103.jac.invOK = true ∧ acceptsUnitSq work3103.out = true := by decide +kernel

def cell3103 : CellCertificate where
  tauBall := tau3103
  contactCenter := center3103
  contactBall := contact3103
  work := work3103
  center_sq := center_sq3103
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3103.1
  jac_ok := checks3103.2.1
  accepted := checks3103.2.2

def cells : List CellCertificate := [cell3096, cell3097, cell3098, cell3099, cell3100, cell3101, cell3102, cell3103]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0387

end


