-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0410
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0410
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:02:42.755328+00:00
-- url     : https://prove2.me/theorems/52464b1b-36d4-48af-9925-edfd1c719e7e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0410` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0410` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0410` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0410 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0410.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0410 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0410

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3280 : RatBall :=
  ⟨⟨-93/640, 233/640⟩, 3/1280⟩
def center3280 : GaussianRat :=
  ⟨-115220153/1000000000, 257805963/1000000000⟩
def contact3280 : RatBall := localContactBall tau3280 center3280
def work3280 : RoundedTauEval :=
  evalTau precision tau3280 contact3280 logTwoBall

theorem center_sq3280 : (center3280.re : ℝ)^2 +
    (center3280.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3280]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3280 : work3280.theta.ok = true ∧
    work3280.jac.invOK = true ∧ acceptsUnitSq work3280.out = true := by decide +kernel

def cell3280 : CellCertificate where
  tauBall := tau3280
  contactCenter := center3280
  contactBall := contact3280
  work := work3280
  center_sq := center_sq3280
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3280.1
  jac_ok := checks3280.2.1
  accepted := checks3280.2.2

def tau3281 : RatBall :=
  ⟨⟨-19/128, 47/128⟩, 3/1280⟩
def center3281 : GaussianRat :=
  ⟨-117937551/1000000000, 649789/2500000⟩
def contact3281 : RatBall := localContactBall tau3281 center3281
def work3281 : RoundedTauEval :=
  evalTau precision tau3281 contact3281 logTwoBall

theorem center_sq3281 : (center3281.re : ℝ)^2 +
    (center3281.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3281]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3281 : work3281.theta.ok = true ∧
    work3281.jac.invOK = true ∧ acceptsUnitSq work3281.out = true := by decide +kernel

def cell3281 : CellCertificate where
  tauBall := tau3281
  contactCenter := center3281
  contactBall := contact3281
  work := work3281
  center_sq := center_sq3281
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3281.1
  jac_ok := checks3281.2.1
  accepted := checks3281.2.2

def tau3282 : RatBall :=
  ⟨⟨-93/640, 47/128⟩, 3/1280⟩
def center3282 : GaussianRat :=
  ⟨-115521207/1000000000, 32527691/125000000⟩
def contact3282 : RatBall := localContactBall tau3282 center3282
def work3282 : RoundedTauEval :=
  evalTau precision tau3282 contact3282 logTwoBall

theorem center_sq3282 : (center3282.re : ℝ)^2 +
    (center3282.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3282]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3282 : work3282.theta.ok = true ∧
    work3282.jac.invOK = true ∧ acceptsUnitSq work3282.out = true := by decide +kernel

def cell3282 : CellCertificate where
  tauBall := tau3282
  contactCenter := center3282
  contactBall := contact3282
  work := work3282
  center_sq := center_sq3282
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3282.1
  jac_ok := checks3282.2.1
  accepted := checks3282.2.2

def tau3283 : RatBall :=
  ⟨⟨-91/640, 233/640⟩, 3/1280⟩
def center3283 : GaussianRat :=
  ⟨-112805403/1000000000, 25810217/100000000⟩
def contact3283 : RatBall := localContactBall tau3283 center3283
def work3283 : RoundedTauEval :=
  evalTau precision tau3283 contact3283 logTwoBall

theorem center_sq3283 : (center3283.re : ℝ)^2 +
    (center3283.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3283]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3283 : work3283.theta.ok = true ∧
    work3283.jac.invOK = true ∧ acceptsUnitSq work3283.out = true := by decide +kernel

def cell3283 : CellCertificate where
  tauBall := tau3283
  contactCenter := center3283
  contactBall := contact3283
  work := work3283
  center_sq := center_sq3283
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3283.1
  jac_ok := checks3283.2.1
  accepted := checks3283.2.2

def tau3284 : RatBall :=
  ⟨⟨-89/640, 233/640⟩, 3/1280⟩
def center3284 : GaussianRat :=
  ⟨-22077337/200000000, 258392707/1000000000⟩
def contact3284 : RatBall := localContactBall tau3284 center3284
def work3284 : RoundedTauEval :=
  evalTau precision tau3284 contact3284 logTwoBall

theorem center_sq3284 : (center3284.re : ℝ)^2 +
    (center3284.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3284]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3284 : work3284.theta.ok = true ∧
    work3284.jac.invOK = true ∧ acceptsUnitSq work3284.out = true := by decide +kernel

def cell3284 : CellCertificate where
  tauBall := tau3284
  contactCenter := center3284
  contactBall := contact3284
  work := work3284
  center_sq := center_sq3284
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3284.1
  jac_ok := checks3284.2.1
  accepted := checks3284.2.2

def tau3285 : RatBall :=
  ⟨⟨-91/640, 47/128⟩, 3/1280⟩
def center3285 : GaussianRat :=
  ⟨-14137597/125000000, 260521763/1000000000⟩
def contact3285 : RatBall := localContactBall tau3285 center3285
def work3285 : RoundedTauEval :=
  evalTau precision tau3285 contact3285 logTwoBall

theorem center_sq3285 : (center3285.re : ℝ)^2 +
    (center3285.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3285]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3285 : work3285.theta.ok = true ∧
    work3285.jac.invOK = true ∧ acceptsUnitSq work3285.out = true := by decide +kernel

def cell3285 : CellCertificate where
  tauBall := tau3285
  contactCenter := center3285
  contactBall := contact3285
  work := work3285
  center_sq := center_sq3285
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3285.1
  jac_ok := checks3285.2.1
  accepted := checks3285.2.2

def tau3286 : RatBall :=
  ⟨⟨-89/640, 47/128⟩, 3/1280⟩
def center3286 : GaussianRat :=
  ⟨-110676327/1000000000, 2037627/7812500⟩
def contact3286 : RatBall := localContactBall tau3286 center3286
def work3286 : RoundedTauEval :=
  evalTau precision tau3286 contact3286 logTwoBall

theorem center_sq3286 : (center3286.re : ℝ)^2 +
    (center3286.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3286]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3286 : work3286.theta.ok = true ∧
    work3286.jac.invOK = true ∧ acceptsUnitSq work3286.out = true := by decide +kernel

def cell3286 : CellCertificate where
  tauBall := tau3286
  contactCenter := center3286
  contactBall := contact3286
  work := work3286
  center_sq := center_sq3286
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3286.1
  jac_ok := checks3286.2.1
  accepted := checks3286.2.2

def tau3287 : RatBall :=
  ⟨⟨-19/128, 237/640⟩, 3/1280⟩
def center3287 : GaussianRat :=
  ⟨-29562099/250000000, 262332709/1000000000⟩
def contact3287 : RatBall := localContactBall tau3287 center3287
def work3287 : RoundedTauEval :=
  evalTau precision tau3287 contact3287 logTwoBall

theorem center_sq3287 : (center3287.re : ℝ)^2 +
    (center3287.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3287]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3287 : work3287.theta.ok = true ∧
    work3287.jac.invOK = true ∧ acceptsUnitSq work3287.out = true := by decide +kernel

def cell3287 : CellCertificate where
  tauBall := tau3287
  contactCenter := center3287
  contactBall := contact3287
  work := work3287
  center_sq := center_sq3287
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3287.1
  jac_ok := checks3287.2.1
  accepted := checks3287.2.2

def cells : List CellCertificate := [cell3280, cell3281, cell3282, cell3283, cell3284, cell3285, cell3286, cell3287]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0410

end


