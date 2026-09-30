-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0301_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0301_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:26:37.274206+00:00
-- url     : https://prove2.me/theorems/69ac35a3-1d89-4c20-a0f1-1c61b7f29dd1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0301 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0301 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0301 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0301 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0301 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0301

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2408 : RatBall :=
  ⟨⟨37/320, 117/320⟩, 3/640⟩
def center2408 : GaussianRat :=
  ⟨46124689/500000000, 261610997/1000000000⟩
def contact2408 : RatBall := localContactBall tau2408 center2408
def work2408 : RoundedTauEval :=
  evalTau precision tau2408 contact2408 logTwoBall

theorem center_sq2408 : (center2408.re : ℝ)^2 +
    (center2408.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2408]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2408 : work2408.theta.ok = true ∧
    work2408.jac.invOK = true ∧ acceptsUnitSq work2408.out = true := by decide +kernel

def cell2408 : CellCertificate where
  tauBall := tau2408
  contactCenter := center2408
  contactBall := contact2408
  work := work2408
  center_sq := center_sq2408
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2408.1
  jac_ok := checks2408.2.1
  accepted := checks2408.2.2

def tau2409 : RatBall :=
  ⟨⟨39/320, 117/320⟩, 3/640⟩
def center2409 : GaussianRat :=
  ⟨97144261/1000000000, 261108469/1000000000⟩
def contact2409 : RatBall := localContactBall tau2409 center2409
def work2409 : RoundedTauEval :=
  evalTau precision tau2409 contact2409 logTwoBall

theorem center_sq2409 : (center2409.re : ℝ)^2 +
    (center2409.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2409]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2409 : work2409.theta.ok = true ∧
    work2409.jac.invOK = true ∧ acceptsUnitSq work2409.out = true := by decide +kernel

def cell2409 : CellCertificate where
  tauBall := tau2409
  contactCenter := center2409
  contactBall := contact2409
  work := work2409
  center_sq := center_sq2409
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2409.1
  jac_ok := checks2409.2.1
  accepted := checks2409.2.2

def tau2410 : RatBall :=
  ⟨⟨41/320, 113/320⟩, 3/640⟩
def center2410 : GaussianRat :=
  ⟨100977067/1000000000, 250881183/1000000000⟩
def contact2410 : RatBall := localContactBall tau2410 center2410
def work2410 : RoundedTauEval :=
  evalTau precision tau2410 contact2410 logTwoBall

theorem center_sq2410 : (center2410.re : ℝ)^2 +
    (center2410.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2410]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2410 : work2410.theta.ok = true ∧
    work2410.jac.invOK = true ∧ acceptsUnitSq work2410.out = true := by decide +kernel

def cell2410 : CellCertificate where
  tauBall := tau2410
  contactCenter := center2410
  contactBall := contact2410
  work := work2410
  center_sq := center_sq2410
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2410.1
  jac_ok := checks2410.2.1
  accepted := checks2410.2.2

def tau2411 : RatBall :=
  ⟨⟨43/320, 113/320⟩, 3/640⟩
def center2411 : GaussianRat :=
  ⟨105797499/1000000000, 62590039/250000000⟩
def contact2411 : RatBall := localContactBall tau2411 center2411
def work2411 : RoundedTauEval :=
  evalTau precision tau2411 contact2411 logTwoBall

theorem center_sq2411 : (center2411.re : ℝ)^2 +
    (center2411.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2411]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2411 : work2411.theta.ok = true ∧
    work2411.jac.invOK = true ∧ acceptsUnitSq work2411.out = true := by decide +kernel

def cell2411 : CellCertificate where
  tauBall := tau2411
  contactCenter := center2411
  contactBall := contact2411
  work := work2411
  center_sq := center_sq2411
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2411.1
  jac_ok := checks2411.2.1
  accepted := checks2411.2.2

def tau2412 : RatBall :=
  ⟨⟨41/320, 23/64⟩, 3/640⟩
def center2412 : GaussianRat :=
  ⟨12686743/125000000, 255720023/1000000000⟩
def contact2412 : RatBall := localContactBall tau2412 center2412
def work2412 : RoundedTauEval :=
  evalTau precision tau2412 contact2412 logTwoBall

theorem center_sq2412 : (center2412.re : ℝ)^2 +
    (center2412.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2412]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2412 : work2412.theta.ok = true ∧
    work2412.jac.invOK = true ∧ acceptsUnitSq work2412.out = true := by decide +kernel

def cell2412 : CellCertificate where
  tauBall := tau2412
  contactCenter := center2412
  contactBall := contact2412
  work := work2412
  center_sq := center_sq2412
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2412.1
  jac_ok := checks2412.2.1
  accepted := checks2412.2.2

def tau2413 : RatBall :=
  ⟨⟨43/320, 23/64⟩, 3/640⟩
def center2413 : GaussianRat :=
  ⟨106336973/1000000000, 255184583/1000000000⟩
def contact2413 : RatBall := localContactBall tau2413 center2413
def work2413 : RoundedTauEval :=
  evalTau precision tau2413 contact2413 logTwoBall

theorem center_sq2413 : (center2413.re : ℝ)^2 +
    (center2413.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2413]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2413 : work2413.theta.ok = true ∧
    work2413.jac.invOK = true ∧ acceptsUnitSq work2413.out = true := by decide +kernel

def cell2413 : CellCertificate where
  tauBall := tau2413
  contactCenter := center2413
  contactBall := contact2413
  work := work2413
  center_sq := center_sq2413
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2413.1
  jac_ok := checks2413.2.1
  accepted := checks2413.2.2

def tau2414 : RatBall :=
  ⟨⟨9/64, 113/320⟩, 3/640⟩
def center2414 : GaussianRat :=
  ⟨22120681/200000000, 249816993/1000000000⟩
def contact2414 : RatBall := localContactBall tau2414 center2414

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0301


