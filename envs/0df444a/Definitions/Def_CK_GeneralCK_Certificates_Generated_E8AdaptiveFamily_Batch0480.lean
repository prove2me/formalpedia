-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0480
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0480
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:27:12.171618+00:00
-- url     : https://prove2.me/theorems/6226413e-0828-45a0-80a5-6e2c49d84540
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0480` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0480` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0480` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0480 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0480.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0480 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0480

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3840 : RatBall :=
  ⟨⟨129/640, 221/640⟩, 3/1280⟩
def center3840 : GaussianRat :=
  ⟨155670749/1000000000, 118833343/500000000⟩
def contact3840 : RatBall := localContactBall tau3840 center3840
def work3840 : RoundedTauEval :=
  evalTau precision tau3840 contact3840 logTwoBall

theorem center_sq3840 : (center3840.re : ℝ)^2 +
    (center3840.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3840]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3840 : work3840.theta.ok = true ∧
    work3840.jac.invOK = true ∧ acceptsUnitSq work3840.out = true := by decide +kernel

def cell3840 : CellCertificate where
  tauBall := tau3840
  contactCenter := center3840
  contactBall := contact3840
  work := work3840
  center_sq := center_sq3840
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3840.1
  jac_ok := checks3840.2.1
  accepted := checks3840.2.2

def tau3841 : RatBall :=
  ⟨⟨131/640, 221/640⟩, 3/1280⟩
def center3841 : GaussianRat :=
  ⟨157970893/1000000000, 237302543/1000000000⟩
def contact3841 : RatBall := localContactBall tau3841 center3841
def work3841 : RoundedTauEval :=
  evalTau precision tau3841 contact3841 logTwoBall

theorem center_sq3841 : (center3841.re : ℝ)^2 +
    (center3841.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3841]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3841 : work3841.theta.ok = true ∧
    work3841.jac.invOK = true ∧ acceptsUnitSq work3841.out = true := by decide +kernel

def cell3841 : CellCertificate where
  tauBall := tau3841
  contactCenter := center3841
  contactBall := contact3841
  work := work3841
  center_sq := center_sq3841
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3841.1
  jac_ok := checks3841.2.1
  accepted := checks3841.2.2

def tau3842 : RatBall :=
  ⟨⟨137/640, 217/640⟩, 3/1280⟩
def center3842 : GaussianRat :=
  ⟨41023473/250000000, 231626927/1000000000⟩
def contact3842 : RatBall := localContactBall tau3842 center3842
def work3842 : RoundedTauEval :=
  evalTau precision tau3842 contact3842 logTwoBall

theorem center_sq3842 : (center3842.re : ℝ)^2 +
    (center3842.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3842]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3842 : work3842.theta.ok = true ∧
    work3842.jac.invOK = true ∧ acceptsUnitSq work3842.out = true := by decide +kernel

def cell3842 : CellCertificate where
  tauBall := tau3842
  contactCenter := center3842
  contactBall := contact3842
  work := work3842
  center_sq := center_sq3842
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3842.1
  jac_ok := checks3842.2.1
  accepted := checks3842.2.2

def tau3843 : RatBall :=
  ⟨⟨149/640, 209/640⟩, 3/1280⟩
def center3843 : GaussianRat :=
  ⟨176122773/1000000000, 220393101/1000000000⟩
def contact3843 : RatBall := localContactBall tau3843 center3843
def work3843 : RoundedTauEval :=
  evalTau precision tau3843 contact3843 logTwoBall

theorem center_sq3843 : (center3843.re : ℝ)^2 +
    (center3843.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3843]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3843 : work3843.theta.ok = true ∧
    work3843.jac.invOK = true ∧ acceptsUnitSq work3843.out = true := by decide +kernel

def cell3843 : CellCertificate where
  tauBall := tau3843
  contactCenter := center3843
  contactBall := contact3843
  work := work3843
  center_sq := center_sq3843
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3843.1
  jac_ok := checks3843.2.1
  accepted := checks3843.2.2

def cells : List CellCertificate := [cell3840, cell3841, cell3842, cell3843]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0480

end


