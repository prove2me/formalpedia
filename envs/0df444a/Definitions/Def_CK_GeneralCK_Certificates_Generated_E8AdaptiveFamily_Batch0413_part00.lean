-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0413_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0413_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:14:09.648397+00:00
-- url     : https://prove2.me/theorems/f9631971-8ff8-448c-9f57-4b647b87d0a3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0413 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3304 : RatBall :=
  ⟨⟨-17/128, 237/640⟩, 3/1280⟩
def center3304 : GaussianRat :=
  ⟨-106097509/1000000000, 131912477/500000000⟩
def contact3304 : RatBall := localContactBall tau3304 center3304
def work3304 : RoundedTauEval :=
  evalTau precision tau3304 contact3304 logTwoBall

theorem center_sq3304 : (center3304.re : ℝ)^2 +
    (center3304.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3304]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3304 : work3304.theta.ok = true ∧
    work3304.jac.invOK = true ∧ acceptsUnitSq work3304.out = true := by decide +kernel

def cell3304 : CellCertificate where
  tauBall := tau3304
  contactCenter := center3304
  contactBall := contact3304
  work := work3304
  center_sq := center_sq3304
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3304.1
  jac_ok := checks3304.2.1
  accepted := checks3304.2.2

def tau3305 : RatBall :=
  ⟨⟨-87/640, 239/640⟩, 3/1280⟩
def center3305 : GaussianRat :=
  ⟨-4353093/40000000, 53195483/200000000⟩
def contact3305 : RatBall := localContactBall tau3305 center3305
def work3305 : RoundedTauEval :=
  evalTau precision tau3305 contact3305 logTwoBall

theorem center_sq3305 : (center3305.re : ℝ)^2 +
    (center3305.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3305]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3305 : work3305.theta.ok = true ∧
    work3305.jac.invOK = true ∧ acceptsUnitSq work3305.out = true := by decide +kernel

def cell3305 : CellCertificate where
  tauBall := tau3305
  contactCenter := center3305
  contactBall := contact3305
  work := work3305
  center_sq := center_sq3305
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3305.1
  jac_ok := checks3305.2.1
  accepted := checks3305.2.2

def tau3306 : RatBall :=
  ⟨⟨-17/128, 239/640⟩, 3/1280⟩
def center3306 : GaussianRat :=
  ⟨-10638319/100000000, 266268043/1000000000⟩
def contact3306 : RatBall := localContactBall tau3306 center3306
def work3306 : RoundedTauEval :=
  evalTau precision tau3306 contact3306 logTwoBall

theorem center_sq3306 : (center3306.re : ℝ)^2 +
    (center3306.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3306]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3306 : work3306.theta.ok = true ∧
    work3306.jac.invOK = true ∧ acceptsUnitSq work3306.out = true := by decide +kernel

def cell3306 : CellCertificate where
  tauBall := tau3306
  contactCenter := center3306
  contactBall := contact3306
  work := work3306
  center_sq := center_sq3306
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3306.1
  jac_ok := checks3306.2.1
  accepted := checks3306.2.2

def tau3307 : RatBall :=
  ⟨⟨-83/640, 237/640⟩, 3/1280⟩
def center3307 : GaussianRat :=
  ⟨-6478469/62500000, 132052859/500000000⟩
def contact3307 : RatBall := localContactBall tau3307 center3307
def work3307 : RoundedTauEval :=
  evalTau precision tau3307 contact3307 logTwoBall

theorem center_sq3307 : (center3307.re : ℝ)^2 +
    (center3307.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3307]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3307 : work3307.theta.ok = true ∧
    work3307.jac.invOK = true ∧ acceptsUnitSq work3307.out = true := by decide +kernel

def cell3307 : CellCertificate where
  tauBall := tau3307
  contactCenter := center3307
  contactBall := contact3307
  work := work3307
  center_sq := center_sq3307
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3307.1
  jac_ok := checks3307.2.1
  accepted := checks3307.2.2

def tau3308 : RatBall :=
  ⟨⟨-81/640, 237/640⟩, 3/1280⟩
def center3308 : GaussianRat :=
  ⟨-101209731/1000000000, 10575219/40000000⟩
def contact3308 : RatBall := localContactBall tau3308 center3308

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413


