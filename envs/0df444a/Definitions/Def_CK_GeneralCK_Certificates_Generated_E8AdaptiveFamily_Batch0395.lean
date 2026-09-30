-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0395
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0395
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:50:29.468872+00:00
-- url     : https://prove2.me/theorems/75ceda0b-70ff-4a3f-bd7c-a5a8c516c49b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0395.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0395_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3164 : (center3164.re : ℝ)^2 +
    (center3164.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3164]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3164 : work3164.theta.ok = true ∧
    work3164.jac.invOK = true ∧ acceptsUnitSq work3164.out = true := by decide +kernel

def cell3164 : CellCertificate where
  tauBall := tau3164
  contactCenter := center3164
  contactBall := contact3164
  work := work3164
  center_sq := center_sq3164
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3164.1
  jac_ok := checks3164.2.1
  accepted := checks3164.2.2

def tau3165 : RatBall :=
  ⟨⟨111/640, -45/128⟩, 3/1280⟩
def center3165 : GaussianRat :=
  ⟨67704553/500000000, -6135977/25000000⟩
def contact3165 : RatBall := localContactBall tau3165 center3165
def work3165 : RoundedTauEval :=
  evalTau precision tau3165 contact3165 logTwoBall

theorem center_sq3165 : (center3165.re : ℝ)^2 +
    (center3165.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3165]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3165 : work3165.theta.ok = true ∧
    work3165.jac.invOK = true ∧ acceptsUnitSq work3165.out = true := by decide +kernel

def cell3165 : CellCertificate where
  tauBall := tau3165
  contactCenter := center3165
  contactBall := contact3165
  work := work3165
  center_sq := center_sq3165
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3165.1
  jac_ok := checks3165.2.1
  accepted := checks3165.2.2

def tau3166 : RatBall :=
  ⟨⟨113/640, -231/640⟩, 3/1280⟩
def center3166 : GaussianRat :=
  ⟨138783923/1000000000, -252176463/1000000000⟩
def contact3166 : RatBall := localContactBall tau3166 center3166
def work3166 : RoundedTauEval :=
  evalTau precision tau3166 contact3166 logTwoBall

theorem center_sq3166 : (center3166.re : ℝ)^2 +
    (center3166.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3166]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3166 : work3166.theta.ok = true ∧
    work3166.jac.invOK = true ∧ acceptsUnitSq work3166.out = true := by decide +kernel

def cell3166 : CellCertificate where
  tauBall := tau3166
  contactCenter := center3166
  contactBall := contact3166
  work := work3166
  center_sq := center_sq3166
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3166.1
  jac_ok := checks3166.2.1
  accepted := checks3166.2.2

def tau3167 : RatBall :=
  ⟨⟨113/640, -229/640⟩, 3/1280⟩
def center3167 : GaussianRat :=
  ⟨69219087/500000000, -49963011/200000000⟩
def contact3167 : RatBall := localContactBall tau3167 center3167
def work3167 : RoundedTauEval :=
  evalTau precision tau3167 contact3167 logTwoBall

theorem center_sq3167 : (center3167.re : ℝ)^2 +
    (center3167.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3167]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3167 : work3167.theta.ok = true ∧
    work3167.jac.invOK = true ∧ acceptsUnitSq work3167.out = true := by decide +kernel

def cell3167 : CellCertificate where
  tauBall := tau3167
  contactCenter := center3167
  contactBall := contact3167
  work := work3167
  center_sq := center_sq3167
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3167.1
  jac_ok := checks3167.2.1
  accepted := checks3167.2.2

def cells : List CellCertificate := [cell3160, cell3161, cell3162, cell3163, cell3164, cell3165, cell3166, cell3167]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395


