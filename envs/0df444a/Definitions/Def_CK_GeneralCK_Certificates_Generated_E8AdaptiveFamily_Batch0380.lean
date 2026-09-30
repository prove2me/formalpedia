-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0380
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0380
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:48:20.438711+00:00
-- url     : https://prove2.me/theorems/b7b40f05-7266-4220-b698-b3a7ee36986e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0380.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0380_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3044 : (center3044.re : ℝ)^2 +
    (center3044.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3044]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3044 : work3044.theta.ok = true ∧
    work3044.jac.invOK = true ∧ acceptsUnitSq work3044.out = true := by decide +kernel

def cell3044 : CellCertificate where
  tauBall := tau3044
  contactCenter := center3044
  contactBall := contact3044
  work := work3044
  center_sq := center_sq3044
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3044.1
  jac_ok := checks3044.2.1
  accepted := checks3044.2.2

def tau3045 : RatBall :=
  ⟨⟨61/640, -241/640⟩, 3/1280⟩
def center3045 : GaussianRat :=
  ⟨38493039/500000000, -67940497/250000000⟩
def contact3045 : RatBall := localContactBall tau3045 center3045
def work3045 : RoundedTauEval :=
  evalTau precision tau3045 contact3045 logTwoBall

theorem center_sq3045 : (center3045.re : ℝ)^2 +
    (center3045.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3045]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3045 : work3045.theta.ok = true ∧
    work3045.jac.invOK = true ∧ acceptsUnitSq work3045.out = true := by decide +kernel

def cell3045 : CellCertificate where
  tauBall := tau3045
  contactCenter := center3045
  contactBall := contact3045
  work := work3045
  center_sq := center_sq3045
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3045.1
  jac_ok := checks3045.2.1
  accepted := checks3045.2.2

def tau3046 : RatBall :=
  ⟨⟨63/640, -241/640⟩, 3/1280⟩
def center3046 : GaussianRat :=
  ⟨15895643/200000000, -271543799/1000000000⟩
def contact3046 : RatBall := localContactBall tau3046 center3046
def work3046 : RoundedTauEval :=
  evalTau precision tau3046 contact3046 logTwoBall

theorem center_sq3046 : (center3046.re : ℝ)^2 +
    (center3046.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3046]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3046 : work3046.theta.ok = true ∧
    work3046.jac.invOK = true ∧ acceptsUnitSq work3046.out = true := by decide +kernel

def cell3046 : CellCertificate where
  tauBall := tau3046
  contactCenter := center3046
  contactBall := contact3046
  work := work3046
  center_sq := center_sq3046
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3046.1
  jac_ok := checks3046.2.1
  accepted := checks3046.2.2

def tau3047 : RatBall :=
  ⟨⟨13/128, -247/640⟩, 3/1280⟩
def center3047 : GaussianRat :=
  ⟨82665793/1000000000, -278811601/1000000000⟩
def contact3047 : RatBall := localContactBall tau3047 center3047
def work3047 : RoundedTauEval :=
  evalTau precision tau3047 contact3047 logTwoBall

theorem center_sq3047 : (center3047.re : ℝ)^2 +
    (center3047.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3047]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3047 : work3047.theta.ok = true ∧
    work3047.jac.invOK = true ∧ acceptsUnitSq work3047.out = true := by decide +kernel

def cell3047 : CellCertificate where
  tauBall := tau3047
  contactCenter := center3047
  contactBall := contact3047
  work := work3047
  center_sq := center_sq3047
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3047.1
  jac_ok := checks3047.2.1
  accepted := checks3047.2.2

def cells : List CellCertificate := [cell3040, cell3041, cell3042, cell3043, cell3044, cell3045, cell3046, cell3047]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380


