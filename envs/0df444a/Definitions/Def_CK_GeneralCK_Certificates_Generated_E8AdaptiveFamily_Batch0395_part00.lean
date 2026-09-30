-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0395_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0395_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:02:45.667779+00:00
-- url     : https://prove2.me/theorems/4a59bb76-8240-4aa8-985a-5f2e357a63aa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0395 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3160 : RatBall :=
  ⟨⟨109/640, -229/640⟩, 3/1280⟩
def center3160 : GaussianRat :=
  ⟨133711273/1000000000, -250491903/1000000000⟩
def contact3160 : RatBall := localContactBall tau3160 center3160
def work3160 : RoundedTauEval :=
  evalTau precision tau3160 contact3160 logTwoBall

theorem center_sq3160 : (center3160.re : ℝ)^2 +
    (center3160.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3160]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3160 : work3160.theta.ok = true ∧
    work3160.jac.invOK = true ∧ acceptsUnitSq work3160.out = true := by decide +kernel

def cell3160 : CellCertificate where
  tauBall := tau3160
  contactCenter := center3160
  contactBall := contact3160
  work := work3160
  center_sq := center_sq3160
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3160.1
  jac_ok := checks3160.2.1
  accepted := checks3160.2.2

def tau3161 : RatBall :=
  ⟨⟨111/640, -229/640⟩, 3/1280⟩
def center3161 : GaussianRat :=
  ⟨136076987/1000000000, -250155999/1000000000⟩
def contact3161 : RatBall := localContactBall tau3161 center3161
def work3161 : RoundedTauEval :=
  evalTau precision tau3161 contact3161 logTwoBall

theorem center_sq3161 : (center3161.re : ℝ)^2 +
    (center3161.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3161]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3161 : work3161.theta.ok = true ∧
    work3161.jac.invOK = true ∧ acceptsUnitSq work3161.out = true := by decide +kernel

def cell3161 : CellCertificate where
  tauBall := tau3161
  contactCenter := center3161
  contactBall := contact3161
  work := work3161
  center_sq := center_sq3161
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3161.1
  jac_ok := checks3161.2.1
  accepted := checks3161.2.2

def tau3162 : RatBall :=
  ⟨⟨109/640, -227/640⟩, 3/1280⟩
def center3162 : GaussianRat :=
  ⟨133380131/1000000000, -248126483/1000000000⟩
def contact3162 : RatBall := localContactBall tau3162 center3162
def work3162 : RoundedTauEval :=
  evalTau precision tau3162 contact3162 logTwoBall

theorem center_sq3162 : (center3162.re : ℝ)^2 +
    (center3162.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3162]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3162 : work3162.theta.ok = true ∧
    work3162.jac.invOK = true ∧ acceptsUnitSq work3162.out = true := by decide +kernel

def cell3162 : CellCertificate where
  tauBall := tau3162
  contactCenter := center3162
  contactBall := contact3162
  work := work3162
  center_sq := center_sq3162
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3162.1
  jac_ok := checks3162.2.1
  accepted := checks3162.2.2

def tau3163 : RatBall :=
  ⟨⟨111/640, -227/640⟩, 3/1280⟩
def center3163 : GaussianRat :=
  ⟨135740809/1000000000, -4955901/20000000⟩
def contact3163 : RatBall := localContactBall tau3163 center3163
def work3163 : RoundedTauEval :=
  evalTau precision tau3163 contact3163 logTwoBall

theorem center_sq3163 : (center3163.re : ℝ)^2 +
    (center3163.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3163]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3163 : work3163.theta.ok = true ∧
    work3163.jac.invOK = true ∧ acceptsUnitSq work3163.out = true := by decide +kernel

def cell3163 : CellCertificate where
  tauBall := tau3163
  contactCenter := center3163
  contactBall := contact3163
  work := work3163
  center_sq := center_sq3163
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3163.1
  jac_ok := checks3163.2.1
  accepted := checks3163.2.2

def tau3164 : RatBall :=
  ⟨⟨109/640, -45/128⟩, 3/1280⟩
def center3164 : GaussianRat :=
  ⟨26610681/200000000, -245766093/1000000000⟩
def contact3164 : RatBall := localContactBall tau3164 center3164
def work3164 : RoundedTauEval :=
  evalTau precision tau3164 contact3164 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395


