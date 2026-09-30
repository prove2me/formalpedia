-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0397
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0397
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:54:35.608982+00:00
-- url     : https://prove2.me/theorems/a2d38378-769e-47d4-9d31-e9744a9c2286
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0397.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0397_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3180 : (center3180.re : ℝ)^2 +
    (center3180.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3180]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3180 : work3180.theta.ok = true ∧
    work3180.jac.invOK = true ∧ acceptsUnitSq work3180.out = true := by decide +kernel

def cell3180 : CellCertificate where
  tauBall := tau3180
  contactCenter := center3180
  contactBall := contact3180
  work := work3180
  center_sq := center_sq3180
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3180.1
  jac_ok := checks3180.2.1
  accepted := checks3180.2.2

def tau3181 : RatBall :=
  ⟨⟨121/640, -223/640⟩, 3/1280⟩
def center3181 : GaussianRat :=
  ⟨146768957/1000000000, -60350721/250000000⟩
def contact3181 : RatBall := localContactBall tau3181 center3181
def work3181 : RoundedTauEval :=
  evalTau precision tau3181 contact3181 logTwoBall

theorem center_sq3181 : (center3181.re : ℝ)^2 +
    (center3181.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3181]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3181 : work3181.theta.ok = true ∧
    work3181.jac.invOK = true ∧ acceptsUnitSq work3181.out = true := by decide +kernel

def cell3181 : CellCertificate where
  tauBall := tau3181
  contactCenter := center3181
  contactBall := contact3181
  work := work3181
  center_sq := center_sq3181
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3181.1
  jac_ok := checks3181.2.1
  accepted := checks3181.2.2

def tau3182 : RatBall :=
  ⟨⟨123/640, -223/640⟩, 3/1280⟩
def center3182 : GaussianRat :=
  ⟨74546313/500000000, -120525907/500000000⟩
def contact3182 : RatBall := localContactBall tau3182 center3182
def work3182 : RoundedTauEval :=
  evalTau precision tau3182 contact3182 logTwoBall

theorem center_sq3182 : (center3182.re : ℝ)^2 +
    (center3182.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3182]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3182 : work3182.theta.ok = true ∧
    work3182.jac.invOK = true ∧ acceptsUnitSq work3182.out = true := by decide +kernel

def cell3182 : CellCertificate where
  tauBall := tau3182
  contactCenter := center3182
  contactBall := contact3182
  work := work3182
  center_sq := center_sq3182
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3182.1
  jac_ok := checks3182.2.1
  accepted := checks3182.2.2

def tau3183 : RatBall :=
  ⟨⟨121/640, -221/640⟩, 3/1280⟩
def center3183 : GaussianRat :=
  ⟨146422507/1000000000, -9563167/40000000⟩
def contact3183 : RatBall := localContactBall tau3183 center3183
def work3183 : RoundedTauEval :=
  evalTau precision tau3183 contact3183 logTwoBall

theorem center_sq3183 : (center3183.re : ℝ)^2 +
    (center3183.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3183]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3183 : work3183.theta.ok = true ∧
    work3183.jac.invOK = true ∧ acceptsUnitSq work3183.out = true := by decide +kernel

def cell3183 : CellCertificate where
  tauBall := tau3183
  contactCenter := center3183
  contactBall := contact3183
  work := work3183
  center_sq := center_sq3183
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3183.1
  jac_ok := checks3183.2.1
  accepted := checks3183.2.2

def cells : List CellCertificate := [cell3176, cell3177, cell3178, cell3179, cell3180, cell3181, cell3182, cell3183]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397


