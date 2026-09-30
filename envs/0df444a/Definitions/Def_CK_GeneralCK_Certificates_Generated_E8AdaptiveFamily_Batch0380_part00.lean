-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0380_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0380_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:04:05.243705+00:00
-- url     : https://prove2.me/theorems/86edf015-8134-41b3-81f4-b4c0c1062e67
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0380 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3040 : RatBall :=
  ⟨⟨59/640, -243/640⟩, 3/1280⟩
def center3040 : GaussianRat :=
  ⟨74700643/1000000000, -13723671/50000000⟩
def contact3040 : RatBall := localContactBall tau3040 center3040
def work3040 : RoundedTauEval :=
  evalTau precision tau3040 contact3040 logTwoBall

theorem center_sq3040 : (center3040.re : ℝ)^2 +
    (center3040.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3040]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3040 : work3040.theta.ok = true ∧
    work3040.jac.invOK = true ∧ acceptsUnitSq work3040.out = true := by decide +kernel

def cell3040 : CellCertificate where
  tauBall := tau3040
  contactCenter := center3040
  contactBall := contact3040
  work := work3040
  center_sq := center_sq3040
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3040.1
  jac_ok := checks3040.2.1
  accepted := checks3040.2.2

def tau3041 : RatBall :=
  ⟨⟨57/640, -241/640⟩, 3/1280⟩
def center3041 : GaussianRat :=
  ⟨1439861/20000000, -68044601/250000000⟩
def contact3041 : RatBall := localContactBall tau3041 center3041
def work3041 : RoundedTauEval :=
  evalTau precision tau3041 contact3041 logTwoBall

theorem center_sq3041 : (center3041.re : ℝ)^2 +
    (center3041.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3041]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3041 : work3041.theta.ok = true ∧
    work3041.jac.invOK = true ∧ acceptsUnitSq work3041.out = true := by decide +kernel

def cell3041 : CellCertificate where
  tauBall := tau3041
  contactCenter := center3041
  contactBall := contact3041
  work := work3041
  center_sq := center_sq3041
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3041.1
  jac_ok := checks3041.2.1
  accepted := checks3041.2.2

def tau3042 : RatBall :=
  ⟨⟨59/640, -241/640⟩, 3/1280⟩
def center3042 : GaussianRat :=
  ⟨37245497/500000000, -8499173/31250000⟩
def contact3042 : RatBall := localContactBall tau3042 center3042
def work3042 : RoundedTauEval :=
  evalTau precision tau3042 contact3042 logTwoBall

theorem center_sq3042 : (center3042.re : ℝ)^2 +
    (center3042.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3042]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3042 : work3042.theta.ok = true ∧
    work3042.jac.invOK = true ∧ acceptsUnitSq work3042.out = true := by decide +kernel

def cell3042 : CellCertificate where
  tauBall := tau3042
  contactCenter := center3042
  contactBall := contact3042
  work := work3042
  center_sq := center_sq3042
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3042.1
  jac_ok := checks3042.2.1
  accepted := checks3042.2.2

def tau3043 : RatBall :=
  ⟨⟨61/640, -243/640⟩, 3/1280⟩
def center3043 : GaussianRat :=
  ⟨77202433/1000000000, -5485179/20000000⟩
def contact3043 : RatBall := localContactBall tau3043 center3043
def work3043 : RoundedTauEval :=
  evalTau precision tau3043 contact3043 logTwoBall

theorem center_sq3043 : (center3043.re : ℝ)^2 +
    (center3043.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3043]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3043 : work3043.theta.ok = true ∧
    work3043.jac.invOK = true ∧ acceptsUnitSq work3043.out = true := by decide +kernel

def cell3043 : CellCertificate where
  tauBall := tau3043
  contactCenter := center3043
  contactBall := contact3043
  work := work3043
  center_sq := center_sq3043
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3043.1
  jac_ok := checks3043.2.1
  accepted := checks3043.2.2

def tau3044 : RatBall :=
  ⟨⟨63/640, -243/640⟩, 3/1280⟩
def center3044 : GaussianRat :=
  ⟨79701237/1000000000, -274037749/1000000000⟩
def contact3044 : RatBall := localContactBall tau3044 center3044
def work3044 : RoundedTauEval :=
  evalTau precision tau3044 contact3044 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380


