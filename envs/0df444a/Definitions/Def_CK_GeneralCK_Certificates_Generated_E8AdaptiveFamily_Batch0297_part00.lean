-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0297_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0297_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:46:49.217663+00:00
-- url     : https://prove2.me/theorems/9f24bcb5-5ca5-4a5e-853f-006a6f089e0b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0297 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2376 : RatBall :=
  ⟨⟨49/320, 109/320⟩, 3/640⟩
def center2376 : GaussianRat :=
  ⟨119007309/1000000000, 59793181/250000000⟩
def contact2376 : RatBall := localContactBall tau2376 center2376
def work2376 : RoundedTauEval :=
  evalTau precision tau2376 contact2376 logTwoBall

theorem center_sq2376 : (center2376.re : ℝ)^2 +
    (center2376.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2376]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2376 : work2376.theta.ok = true ∧
    work2376.jac.invOK = true ∧ acceptsUnitSq work2376.out = true := by decide +kernel

def cell2376 : CellCertificate where
  tauBall := tau2376
  contactCenter := center2376
  contactBall := contact2376
  work := work2376
  center_sq := center_sq2376
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2376.1
  jac_ok := checks2376.2.1
  accepted := checks2376.2.2

def tau2377 : RatBall :=
  ⟨⟨51/320, 109/320⟩, 3/640⟩
def center2377 : GaussianRat :=
  ⟨61862799/500000000, 238597409/1000000000⟩
def contact2377 : RatBall := localContactBall tau2377 center2377
def work2377 : RoundedTauEval :=
  evalTau precision tau2377 contact2377 logTwoBall

theorem center_sq2377 : (center2377.re : ℝ)^2 +
    (center2377.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2377]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2377 : work2377.theta.ok = true ∧
    work2377.jac.invOK = true ∧ acceptsUnitSq work2377.out = true := by decide +kernel

def cell2377 : CellCertificate where
  tauBall := tau2377
  contactCenter := center2377
  contactBall := contact2377
  work := work2377
  center_sq := center_sq2377
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2377.1
  jac_ok := checks2377.2.1
  accepted := checks2377.2.2

def tau2378 : RatBall :=
  ⟨⟨49/320, 111/320⟩, 3/640⟩
def center2378 : GaussianRat :=
  ⟨29895113/250000000, 121954461/500000000⟩
def contact2378 : RatBall := localContactBall tau2378 center2378
def work2378 : RoundedTauEval :=
  evalTau precision tau2378 contact2378 logTwoBall

theorem center_sq2378 : (center2378.re : ℝ)^2 +
    (center2378.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2378]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2378 : work2378.theta.ok = true ∧
    work2378.jac.invOK = true ∧ acceptsUnitSq work2378.out = true := by decide +kernel

def cell2378 : CellCertificate where
  tauBall := tau2378
  contactCenter := center2378
  contactBall := contact2378
  work := work2378
  center_sq := center_sq2378
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2378.1
  jac_ok := checks2378.2.1
  accepted := checks2378.2.2

def tau2379 : RatBall :=
  ⟨⟨51/320, 111/320⟩, 3/640⟩
def center2379 : GaussianRat :=
  ⟨124318847/1000000000, 121658863/500000000⟩
def contact2379 : RatBall := localContactBall tau2379 center2379
def work2379 : RoundedTauEval :=
  evalTau precision tau2379 contact2379 logTwoBall

theorem center_sq2379 : (center2379.re : ℝ)^2 +
    (center2379.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2379]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2379 : work2379.theta.ok = true ∧
    work2379.jac.invOK = true ∧ acceptsUnitSq work2379.out = true := by decide +kernel

def cell2379 : CellCertificate where
  tauBall := tau2379
  contactCenter := center2379
  contactBall := contact2379
  work := work2379
  center_sq := center_sq2379
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2379.1
  jac_ok := checks2379.2.1
  accepted := checks2379.2.2

def tau2380 : RatBall :=
  ⟨⟨53/320, 109/320⟩, 3/640⟩
def center2380 : GaussianRat :=
  ⟨25685587/200000000, 238002417/1000000000⟩
def contact2380 : RatBall := localContactBall tau2380 center2380
def work2380 : RoundedTauEval :=
  evalTau precision tau2380 contact2380 logTwoBall

theorem center_sq2380 : (center2380.re : ℝ)^2 +
    (center2380.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2380]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2380 : work2380.theta.ok = true ∧
    work2380.jac.invOK = true ∧ acceptsUnitSq work2380.out = true := by decide +kernel

def cell2380 : CellCertificate where
  tauBall := tau2380
  contactCenter := center2380
  contactBall := contact2380
  work := work2380
  center_sq := center_sq2380
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2380.1
  jac_ok := checks2380.2.1
  accepted := checks2380.2.2

def tau2381 : RatBall :=
  ⟨⟨11/64, 109/320⟩, 3/640⟩
def center2381 : GaussianRat :=
  ⟨133113831/1000000000, 118694053/500000000⟩
def contact2381 : RatBall := localContactBall tau2381 center2381
def work2381 : RoundedTauEval :=
  evalTau precision tau2381 contact2381 logTwoBall

theorem center_sq2381 : (center2381.re : ℝ)^2 +
    (center2381.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2381]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297


