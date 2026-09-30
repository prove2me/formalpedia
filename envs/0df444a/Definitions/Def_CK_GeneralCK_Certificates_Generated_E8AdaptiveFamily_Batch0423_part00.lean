-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0423_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0423_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:16:13.940741+00:00
-- url     : https://prove2.me/theorems/00c8d005-5fbd-4c36-88f4-f258c1796061
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0423 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3384 : RatBall :=
  ⟨⟨-49/640, 243/640⟩, 3/1280⟩
def center3384 : GaussianRat :=
  ⟨-12430013/200000000, 275443499/1000000000⟩
def contact3384 : RatBall := localContactBall tau3384 center3384
def work3384 : RoundedTauEval :=
  evalTau precision tau3384 contact3384 logTwoBall

theorem center_sq3384 : (center3384.re : ℝ)^2 +
    (center3384.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3384]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3384 : work3384.theta.ok = true ∧
    work3384.jac.invOK = true ∧ acceptsUnitSq work3384.out = true := by decide +kernel

def cell3384 : CellCertificate where
  tauBall := tau3384
  contactCenter := center3384
  contactBall := contact3384
  work := work3384
  center_sq := center_sq3384
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3384.1
  jac_ok := checks3384.2.1
  accepted := checks3384.2.2

def tau3385 : RatBall :=
  ⟨⟨-11/128, 49/128⟩, 3/1280⟩
def center3385 : GaussianRat :=
  ⟨-69887307/1000000000, 277394317/1000000000⟩
def contact3385 : RatBall := localContactBall tau3385 center3385
def work3385 : RoundedTauEval :=
  evalTau precision tau3385 contact3385 logTwoBall

theorem center_sq3385 : (center3385.re : ℝ)^2 +
    (center3385.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3385]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3385 : work3385.theta.ok = true ∧
    work3385.jac.invOK = true ∧ acceptsUnitSq work3385.out = true := by decide +kernel

def cell3385 : CellCertificate where
  tauBall := tau3385
  contactCenter := center3385
  contactBall := contact3385
  work := work3385
  center_sq := center_sq3385
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3385.1
  jac_ok := checks3385.2.1
  accepted := checks3385.2.2

def tau3386 : RatBall :=
  ⟨⟨-53/640, 49/128⟩, 3/1280⟩
def center3386 : GaussianRat :=
  ⟨-4210637/62500000, 55518211/200000000⟩
def contact3386 : RatBall := localContactBall tau3386 center3386
def work3386 : RoundedTauEval :=
  evalTau precision tau3386 contact3386 logTwoBall

theorem center_sq3386 : (center3386.re : ℝ)^2 +
    (center3386.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3386]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3386 : work3386.theta.ok = true ∧
    work3386.jac.invOK = true ∧ acceptsUnitSq work3386.out = true := by decide +kernel

def cell3386 : CellCertificate where
  tauBall := tau3386
  contactCenter := center3386
  contactBall := contact3386
  work := work3386
  center_sq := center_sq3386
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3386.1
  jac_ok := checks3386.2.1
  accepted := checks3386.2.2

def tau3387 : RatBall :=
  ⟨⟨-11/128, 247/640⟩, 3/1280⟩
def center3387 : GaussianRat :=
  ⟨-70088901/1000000000, 139956777/500000000⟩
def contact3387 : RatBall := localContactBall tau3387 center3387
def work3387 : RoundedTauEval :=
  evalTau precision tau3387 contact3387 logTwoBall

theorem center_sq3387 : (center3387.re : ℝ)^2 +
    (center3387.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3387]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3387 : work3387.theta.ok = true ∧
    work3387.jac.invOK = true ∧ acceptsUnitSq work3387.out = true := by decide +kernel

def cell3387 : CellCertificate where
  tauBall := tau3387
  contactCenter := center3387
  contactBall := contact3387
  work := work3387
  center_sq := center_sq3387
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3387.1
  jac_ok := checks3387.2.1
  accepted := checks3387.2.2

def tau3388 : RatBall :=
  ⟨⟨-53/640, 247/640⟩, 3/1280⟩
def center3388 : GaussianRat :=
  ⟨-33782393/500000000, 56022603/200000000⟩
def contact3388 : RatBall := localContactBall tau3388 center3388
def work3388 : RoundedTauEval :=
  evalTau precision tau3388 contact3388 logTwoBall

theorem center_sq3388 : (center3388.re : ℝ)^2 +
    (center3388.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3388]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3388 : work3388.theta.ok = true ∧
    work3388.jac.invOK = true ∧ acceptsUnitSq work3388.out = true := by decide +kernel

def cell3388 : CellCertificate where
  tauBall := tau3388
  contactCenter := center3388
  contactBall := contact3388
  work := work3388
  center_sq := center_sq3388
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3388.1
  jac_ok := checks3388.2.1
  accepted := checks3388.2.2

def tau3389 : RatBall :=
  ⟨⟨-51/640, 49/128⟩, 3/1280⟩
def center3389 : GaussianRat :=
  ⟨-3242521/50000000, 138890411/500000000⟩
def contact3389 : RatBall := localContactBall tau3389 center3389
def work3389 : RoundedTauEval :=
  evalTau precision tau3389 contact3389 logTwoBall

theorem center_sq3389 : (center3389.re : ℝ)^2 +
    (center3389.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3389]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3389 : work3389.theta.ok = true ∧
    work3389.jac.invOK = true ∧ acceptsUnitSq work3389.out = true := by decide +kernel

def cell3389 : CellCertificate where
  tauBall := tau3389
  contactCenter := center3389
  contactBall := contact3389
  work := work3389
  center_sq := center_sq3389
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3389.1
  jac_ok := checks3389.2.1
  accepted := checks3389.2.2

def tau3390 : RatBall :=
  ⟨⟨-49/640, 49/128⟩, 3/1280⟩
def center3390 : GaussianRat :=
  ⟨-31164041/500000000, 277963583/1000000000⟩
def contact3390 : RatBall := localContactBall tau3390 center3390

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423


