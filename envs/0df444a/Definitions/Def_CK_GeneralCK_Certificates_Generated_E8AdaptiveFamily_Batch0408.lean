-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0408
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0408
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:46:14.599866+00:00
-- url     : https://prove2.me/theorems/c0fe1c1c-09b1-48ba-ab76-86d53f3e00fb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0408` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0408` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0408` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0408 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0408.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0408 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0408

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3264 : RatBall :=
  ⟨⟨-21/128, 233/640⟩, 3/1280⟩
def center3264 : GaussianRat :=
  ⟨-8101339/62500000, 3998631/15625000⟩
def contact3264 : RatBall := localContactBall tau3264 center3264
def work3264 : RoundedTauEval :=
  evalTau precision tau3264 contact3264 logTwoBall

theorem center_sq3264 : (center3264.re : ℝ)^2 +
    (center3264.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3264]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3264 : work3264.theta.ok = true ∧
    work3264.jac.invOK = true ∧ acceptsUnitSq work3264.out = true := by decide +kernel

def cell3264 : CellCertificate where
  tauBall := tau3264
  contactCenter := center3264
  contactBall := contact3264
  work := work3264
  center_sq := center_sq3264
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3264.1
  jac_ok := checks3264.2.1
  accepted := checks3264.2.2

def tau3265 : RatBall :=
  ⟨⟨-103/640, 233/640⟩, 3/1280⟩
def center3265 : GaussianRat :=
  ⟨-1987999/15625000, 12812079/50000000⟩
def contact3265 : RatBall := localContactBall tau3265 center3265
def work3265 : RoundedTauEval :=
  evalTau precision tau3265 contact3265 logTwoBall

theorem center_sq3265 : (center3265.re : ℝ)^2 +
    (center3265.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3265]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3265 : work3265.theta.ok = true ∧
    work3265.jac.invOK = true ∧ acceptsUnitSq work3265.out = true := by decide +kernel

def cell3265 : CellCertificate where
  tauBall := tau3265
  contactCenter := center3265
  contactBall := contact3265
  work := work3265
  center_sq := center_sq3265
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3265.1
  jac_ok := checks3265.2.1
  accepted := checks3265.2.2

def tau3266 : RatBall :=
  ⟨⟨-101/640, 233/640⟩, 3/1280⟩
def center3266 : GaussianRat :=
  ⟨-124838069/1000000000, 64141351/250000000⟩
def contact3266 : RatBall := localContactBall tau3266 center3266
def work3266 : RoundedTauEval :=
  evalTau precision tau3266 contact3266 logTwoBall

theorem center_sq3266 : (center3266.re : ℝ)^2 +
    (center3266.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3266]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3266 : work3266.theta.ok = true ∧
    work3266.jac.invOK = true ∧ acceptsUnitSq work3266.out = true := by decide +kernel

def cell3266 : CellCertificate where
  tauBall := tau3266
  contactCenter := center3266
  contactBall := contact3266
  work := work3266
  center_sq := center_sq3266
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3266.1
  jac_ok := checks3266.2.1
  accepted := checks3266.2.2

def tau3267 : RatBall :=
  ⟨⟨-103/640, 47/128⟩, 3/1280⟩
def center3267 : GaussianRat :=
  ⟨-31890163/250000000, 51727193/200000000⟩
def contact3267 : RatBall := localContactBall tau3267 center3267
def work3267 : RoundedTauEval :=
  evalTau precision tau3267 contact3267 logTwoBall

theorem center_sq3267 : (center3267.re : ℝ)^2 +
    (center3267.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3267]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3267 : work3267.theta.ok = true ∧
    work3267.jac.invOK = true ∧ acceptsUnitSq work3267.out = true := by decide +kernel

def cell3267 : CellCertificate where
  tauBall := tau3267
  contactCenter := center3267
  contactBall := contact3267
  work := work3267
  center_sq := center_sq3267
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3267.1
  jac_ok := checks3267.2.1
  accepted := checks3267.2.2

def tau3268 : RatBall :=
  ⟨⟨-101/640, 47/128⟩, 3/1280⟩
def center3268 : GaussianRat :=
  ⟨-25032271/200000000, 809263/3125000⟩
def contact3268 : RatBall := localContactBall tau3268 center3268
def work3268 : RoundedTauEval :=
  evalTau precision tau3268 contact3268 logTwoBall

theorem center_sq3268 : (center3268.re : ℝ)^2 +
    (center3268.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3268]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3268 : work3268.theta.ok = true ∧
    work3268.jac.invOK = true ∧ acceptsUnitSq work3268.out = true := by decide +kernel

def cell3268 : CellCertificate where
  tauBall := tau3268
  contactCenter := center3268
  contactBall := contact3268
  work := work3268
  center_sq := center_sq3268
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3268.1
  jac_ok := checks3268.2.1
  accepted := checks3268.2.2

def tau3269 : RatBall :=
  ⟨⟨-99/640, 233/640⟩, 3/1280⟩
def center3269 : GaussianRat :=
  ⟨-122439891/1000000000, 51376761/200000000⟩
def contact3269 : RatBall := localContactBall tau3269 center3269
def work3269 : RoundedTauEval :=
  evalTau precision tau3269 contact3269 logTwoBall

theorem center_sq3269 : (center3269.re : ℝ)^2 +
    (center3269.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3269]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3269 : work3269.theta.ok = true ∧
    work3269.jac.invOK = true ∧ acceptsUnitSq work3269.out = true := by decide +kernel

def cell3269 : CellCertificate where
  tauBall := tau3269
  contactCenter := center3269
  contactBall := contact3269
  work := work3269
  center_sq := center_sq3269
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3269.1
  jac_ok := checks3269.2.1
  accepted := checks3269.2.2

def tau3270 : RatBall :=
  ⟨⟨-97/640, 233/640⟩, 3/1280⟩
def center3270 : GaussianRat :=
  ⟨-60018733/500000000, 257196731/1000000000⟩
def contact3270 : RatBall := localContactBall tau3270 center3270
def work3270 : RoundedTauEval :=
  evalTau precision tau3270 contact3270 logTwoBall

theorem center_sq3270 : (center3270.re : ℝ)^2 +
    (center3270.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3270]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3270 : work3270.theta.ok = true ∧
    work3270.jac.invOK = true ∧ acceptsUnitSq work3270.out = true := by decide +kernel

def cell3270 : CellCertificate where
  tauBall := tau3270
  contactCenter := center3270
  contactBall := contact3270
  work := work3270
  center_sq := center_sq3270
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3270.1
  jac_ok := checks3270.2.1
  accepted := checks3270.2.2

def tau3271 : RatBall :=
  ⟨⟨-99/640, 47/128⟩, 3/1280⟩
def center3271 : GaussianRat :=
  ⟨-61378847/500000000, 129643433/500000000⟩
def contact3271 : RatBall := localContactBall tau3271 center3271
def work3271 : RoundedTauEval :=
  evalTau precision tau3271 contact3271 logTwoBall

theorem center_sq3271 : (center3271.re : ℝ)^2 +
    (center3271.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3271]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3271 : work3271.theta.ok = true ∧
    work3271.jac.invOK = true ∧ acceptsUnitSq work3271.out = true := by decide +kernel

def cell3271 : CellCertificate where
  tauBall := tau3271
  contactCenter := center3271
  contactBall := contact3271
  work := work3271
  center_sq := center_sq3271
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3271.1
  jac_ok := checks3271.2.1
  accepted := checks3271.2.2

def cells : List CellCertificate := [cell3264, cell3265, cell3266, cell3267, cell3268, cell3269, cell3270, cell3271]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0408

end


