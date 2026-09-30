-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0318_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0318_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:49:41.93901+00:00
-- url     : https://prove2.me/theorems/8d1e390a-28b8-4f89-9e93-1346cf75ef8d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0318 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2544 : RatBall :=
  ⟨⟨73/320, 101/320⟩, 3/640⟩
def center2544 : GaussianRat :=
  ⟨85759271/500000000, 26642441/125000000⟩
def contact2544 : RatBall := localContactBall tau2544 center2544
def work2544 : RoundedTauEval :=
  evalTau precision tau2544 contact2544 logTwoBall

theorem center_sq2544 : (center2544.re : ℝ)^2 +
    (center2544.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2544]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2544 : work2544.theta.ok = true ∧
    work2544.jac.invOK = true ∧ acceptsUnitSq work2544.out = true := by decide +kernel

def cell2544 : CellCertificate where
  tauBall := tau2544
  contactCenter := center2544
  contactBall := contact2544
  work := work2544
  center_sq := center_sq2544
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2544.1
  jac_ok := checks2544.2.1
  accepted := checks2544.2.2

def tau2545 : RatBall :=
  ⟨⟨15/64, 101/320⟩, 3/640⟩
def center2545 : GaussianRat :=
  ⟨21994767/125000000, 212432751/1000000000⟩
def contact2545 : RatBall := localContactBall tau2545 center2545
def work2545 : RoundedTauEval :=
  evalTau precision tau2545 contact2545 logTwoBall

theorem center_sq2545 : (center2545.re : ℝ)^2 +
    (center2545.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2545]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2545 : work2545.theta.ok = true ∧
    work2545.jac.invOK = true ∧ acceptsUnitSq work2545.out = true := by decide +kernel

def cell2545 : CellCertificate where
  tauBall := tau2545
  contactCenter := center2545
  contactBall := contact2545
  work := work2545
  center_sq := center_sq2545
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2545.1
  jac_ok := checks2545.2.1
  accepted := checks2545.2.2

def tau2546 : RatBall :=
  ⟨⟨73/320, 103/320⟩, 3/640⟩
def center2546 : GaussianRat :=
  ⟨34445579/200000000, 217595773/1000000000⟩
def contact2546 : RatBall := localContactBall tau2546 center2546
def work2546 : RoundedTauEval :=
  evalTau precision tau2546 contact2546 logTwoBall

theorem center_sq2546 : (center2546.re : ℝ)^2 +
    (center2546.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2546]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2546 : work2546.theta.ok = true ∧
    work2546.jac.invOK = true ∧ acceptsUnitSq work2546.out = true := by decide +kernel

def cell2546 : CellCertificate where
  tauBall := tau2546
  contactCenter := center2546
  contactBall := contact2546
  work := work2546
  center_sq := center_sq2546
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2546.1
  jac_ok := checks2546.2.1
  accepted := checks2546.2.2

def tau2547 : RatBall :=
  ⟨⟨15/64, 103/320⟩, 3/640⟩
def center2547 : GaussianRat :=
  ⟨44170389/250000000, 43373931/200000000⟩
def contact2547 : RatBall := localContactBall tau2547 center2547
def work2547 : RoundedTauEval :=
  evalTau precision tau2547 contact2547 logTwoBall

theorem center_sq2547 : (center2547.re : ℝ)^2 +
    (center2547.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2547]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2547 : work2547.theta.ok = true ∧
    work2547.jac.invOK = true ∧ acceptsUnitSq work2547.out = true := by decide +kernel

def cell2547 : CellCertificate where
  tauBall := tau2547
  contactCenter := center2547
  contactBall := contact2547
  work := work2547
  center_sq := center_sq2547
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2547.1
  jac_ok := checks2547.2.1
  accepted := checks2547.2.2

def tau2548 : RatBall :=
  ⟨⟨77/320, 101/320⟩, 3/640⟩
def center2548 : GaussianRat :=
  ⟨45094603/250000000, 105856123/500000000⟩
def contact2548 : RatBall := localContactBall tau2548 center2548
def work2548 : RoundedTauEval :=
  evalTau precision tau2548 contact2548 logTwoBall

theorem center_sq2548 : (center2548.re : ℝ)^2 +
    (center2548.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2548]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2548 : work2548.theta.ok = true ∧
    work2548.jac.invOK = true ∧ acceptsUnitSq work2548.out = true := by decide +kernel

def cell2548 : CellCertificate where
  tauBall := tau2548
  contactCenter := center2548
  contactBall := contact2548
  work := work2548
  center_sq := center_sq2548
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2548.1
  jac_ok := checks2548.2.1
  accepted := checks2548.2.2

def tau2549 : RatBall :=
  ⟨⟨79/320, 101/320⟩, 3/640⟩
def center2549 : GaussianRat :=
  ⟨92389531/500000000, 210978373/1000000000⟩
def contact2549 : RatBall := localContactBall tau2549 center2549
def work2549 : RoundedTauEval :=
  evalTau precision tau2549 contact2549 logTwoBall

theorem center_sq2549 : (center2549.re : ℝ)^2 +
    (center2549.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2549]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2549 : work2549.theta.ok = true ∧
    work2549.jac.invOK = true ∧ acceptsUnitSq work2549.out = true := by decide +kernel

def cell2549 : CellCertificate where
  tauBall := tau2549
  contactCenter := center2549
  contactBall := contact2549
  work := work2549
  center_sq := center_sq2549
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2549.1
  jac_ok := checks2549.2.1
  accepted := checks2549.2.2

def tau2550 : RatBall :=
  ⟨⟨77/320, 103/320⟩, 3/640⟩
def center2550 : GaussianRat :=
  ⟨36223107/200000000, 108064747/500000000⟩
def contact2550 : RatBall := localContactBall tau2550 center2550
def work2550 : RoundedTauEval :=
  evalTau precision tau2550 contact2550 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318


