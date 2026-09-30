-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0293_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0293_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:32:44.953214+00:00
-- url     : https://prove2.me/theorems/de8510e1-32a0-4f23-960e-c6195950f41e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0293 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2344 : RatBall :=
  ⟨⟨49/320, 101/320⟩, 3/640⟩
def center2344 : GaussianRat :=
  ⟨3652061/31250000, 220423219/1000000000⟩
def contact2344 : RatBall := localContactBall tau2344 center2344
def work2344 : RoundedTauEval :=
  evalTau precision tau2344 contact2344 logTwoBall

theorem center_sq2344 : (center2344.re : ℝ)^2 +
    (center2344.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2344]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2344 : work2344.theta.ok = true ∧
    work2344.jac.invOK = true ∧ acceptsUnitSq work2344.out = true := by decide +kernel

def cell2344 : CellCertificate where
  tauBall := tau2344
  contactCenter := center2344
  contactBall := contact2344
  work := work2344
  center_sq := center_sq2344
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2344.1
  jac_ok := checks2344.2.1
  accepted := checks2344.2.2

def tau2345 : RatBall :=
  ⟨⟨51/320, 101/320⟩, 3/640⟩
def center2345 : GaussianRat :=
  ⟨30377187/250000000, 6872127/31250000⟩
def contact2345 : RatBall := localContactBall tau2345 center2345
def work2345 : RoundedTauEval :=
  evalTau precision tau2345 contact2345 logTwoBall

theorem center_sq2345 : (center2345.re : ℝ)^2 +
    (center2345.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2345]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2345 : work2345.theta.ok = true ∧
    work2345.jac.invOK = true ∧ acceptsUnitSq work2345.out = true := by decide +kernel

def cell2345 : CellCertificate where
  tauBall := tau2345
  contactCenter := center2345
  contactBall := contact2345
  work := work2345
  center_sq := center_sq2345
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2345.1
  jac_ok := checks2345.2.1
  accepted := checks2345.2.2

def tau2346 : RatBall :=
  ⟨⟨49/320, 103/320⟩, 3/640⟩
def center2346 : GaussianRat :=
  ⟨117379261/1000000000, 56270573/250000000⟩
def contact2346 : RatBall := localContactBall tau2346 center2346
def work2346 : RoundedTauEval :=
  evalTau precision tau2346 contact2346 logTwoBall

theorem center_sq2346 : (center2346.re : ℝ)^2 +
    (center2346.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2346]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2346 : work2346.theta.ok = true ∧
    work2346.jac.invOK = true ∧ acceptsUnitSq work2346.out = true := by decide +kernel

def cell2346 : CellCertificate where
  tauBall := tau2346
  contactCenter := center2346
  contactBall := contact2346
  work := work2346
  center_sq := center_sq2346
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2346.1
  jac_ok := checks2346.2.1
  accepted := checks2346.2.2

def tau2347 : RatBall :=
  ⟨⟨51/320, 103/320⟩, 3/640⟩
def center2347 : GaussianRat :=
  ⟨7627513/62500000, 224552577/1000000000⟩
def contact2347 : RatBall := localContactBall tau2347 center2347
def work2347 : RoundedTauEval :=
  evalTau precision tau2347 contact2347 logTwoBall

theorem center_sq2347 : (center2347.re : ℝ)^2 +
    (center2347.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2347]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2347 : work2347.theta.ok = true ∧
    work2347.jac.invOK = true ∧ acceptsUnitSq work2347.out = true := by decide +kernel

def cell2347 : CellCertificate where
  tauBall := tau2347
  contactCenter := center2347
  contactBall := contact2347
  work := work2347
  center_sq := center_sq2347
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2347.1
  jac_ok := checks2347.2.1
  accepted := checks2347.2.2

def tau2348 : RatBall :=
  ⟨⟨53/320, 101/320⟩, 3/640⟩
def center2348 : GaussianRat :=
  ⟨15767113/125000000, 219375147/1000000000⟩
def contact2348 : RatBall := localContactBall tau2348 center2348
def work2348 : RoundedTauEval :=
  evalTau precision tau2348 contact2348 logTwoBall

theorem center_sq2348 : (center2348.re : ℝ)^2 +
    (center2348.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2348]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2348 : work2348.theta.ok = true ∧
    work2348.jac.invOK = true ∧ acceptsUnitSq work2348.out = true := by decide +kernel

def cell2348 : CellCertificate where
  tauBall := tau2348
  contactCenter := center2348
  contactBall := contact2348
  work := work2348
  center_sq := center_sq2348
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2348.1
  jac_ok := checks2348.2.1
  accepted := checks2348.2.2

def tau2349 : RatBall :=
  ⟨⟨11/64, 101/320⟩, 3/640⟩
def center2349 : GaussianRat :=
  ⟨3268749/25000000, 54706193/250000000⟩
def contact2349 : RatBall := localContactBall tau2349 center2349
def work2349 : RoundedTauEval :=
  evalTau precision tau2349 contact2349 logTwoBall

theorem center_sq2349 : (center2349.re : ℝ)^2 +
    (center2349.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2349]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293


