-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0300
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0300
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:30:11.850789+00:00
-- url     : https://prove2.me/theorems/8b6e393e-a3c0-4a51-abff-86b64dde122b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0300` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0300` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0300` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0300 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0300.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0300 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0300

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2400 : RatBall :=
  ⟨⟨33/320, 23/64⟩, 3/640⟩
def center2400 : GaussianRat :=
  ⟨40992501/500000000, 257627847/1000000000⟩
def contact2400 : RatBall := localContactBall tau2400 center2400
def work2400 : RoundedTauEval :=
  evalTau precision tau2400 contact2400 logTwoBall

theorem center_sq2400 : (center2400.re : ℝ)^2 +
    (center2400.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2400]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2400 : work2400.theta.ok = true ∧
    work2400.jac.invOK = true ∧ acceptsUnitSq work2400.out = true := by decide +kernel

def cell2400 : CellCertificate where
  tauBall := tau2400
  contactCenter := center2400
  contactBall := contact2400
  work := work2400
  center_sq := center_sq2400
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2400.1
  jac_ok := checks2400.2.1
  accepted := checks2400.2.2

def tau2401 : RatBall :=
  ⟨⟨7/64, 23/64⟩, 3/640⟩
def center2401 : GaussianRat :=
  ⟨43440767/500000000, 257186633/1000000000⟩
def contact2401 : RatBall := localContactBall tau2401 center2401
def work2401 : RoundedTauEval :=
  evalTau precision tau2401 contact2401 logTwoBall

theorem center_sq2401 : (center2401.re : ℝ)^2 +
    (center2401.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2401]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2401 : work2401.theta.ok = true ∧
    work2401.jac.invOK = true ∧ acceptsUnitSq work2401.out = true := by decide +kernel

def cell2401 : CellCertificate where
  tauBall := tau2401
  contactCenter := center2401
  contactBall := contact2401
  work := work2401
  center_sq := center_sq2401
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2401.1
  jac_ok := checks2401.2.1
  accepted := checks2401.2.2

def tau2402 : RatBall :=
  ⟨⟨37/320, 113/320⟩, 3/640⟩
def center2402 : GaussianRat :=
  ⟨45647467/500000000, 62963873/250000000⟩
def contact2402 : RatBall := localContactBall tau2402 center2402
def work2402 : RoundedTauEval :=
  evalTau precision tau2402 contact2402 logTwoBall

theorem center_sq2402 : (center2402.re : ℝ)^2 +
    (center2402.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2402]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2402 : work2402.theta.ok = true ∧
    work2402.jac.invOK = true ∧ acceptsUnitSq work2402.out = true := by decide +kernel

def cell2402 : CellCertificate where
  tauBall := tau2402
  contactCenter := center2402
  contactBall := contact2402
  work := work2402
  center_sq := center_sq2402
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2402.1
  jac_ok := checks2402.2.1
  accepted := checks2402.2.2

def tau2403 : RatBall :=
  ⟨⟨39/320, 113/320⟩, 3/640⟩
def center2403 : GaussianRat :=
  ⟨48071341/500000000, 251379737/1000000000⟩
def contact2403 : RatBall := localContactBall tau2403 center2403
def work2403 : RoundedTauEval :=
  evalTau precision tau2403 contact2403 logTwoBall

theorem center_sq2403 : (center2403.re : ℝ)^2 +
    (center2403.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2403]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2403 : work2403.theta.ok = true ∧
    work2403.jac.invOK = true ∧ acceptsUnitSq work2403.out = true := by decide +kernel

def cell2403 : CellCertificate where
  tauBall := tau2403
  contactCenter := center2403
  contactBall := contact2403
  work := work2403
  center_sq := center_sq2403
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2403.1
  jac_ok := checks2403.2.1
  accepted := checks2403.2.2

def tau2404 : RatBall :=
  ⟨⟨37/320, 23/64⟩, 3/640⟩
def center2404 : GaussianRat :=
  ⟨91765617/1000000000, 12836069/50000000⟩
def contact2404 : RatBall := localContactBall tau2404 center2404
def work2404 : RoundedTauEval :=
  evalTau precision tau2404 contact2404 logTwoBall

theorem center_sq2404 : (center2404.re : ℝ)^2 +
    (center2404.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2404]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2404 : work2404.theta.ok = true ∧
    work2404.jac.invOK = true ∧ acceptsUnitSq work2404.out = true := by decide +kernel

def cell2404 : CellCertificate where
  tauBall := tau2404
  contactCenter := center2404
  contactBall := contact2404
  work := work2404
  center_sq := center_sq2404
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2404.1
  jac_ok := checks2404.2.1
  accepted := checks2404.2.2

def tau2405 : RatBall :=
  ⟨⟨39/320, 23/64⟩, 3/640⟩
def center2405 : GaussianRat :=
  ⟨773093/8000000, 128116201/500000000⟩
def contact2405 : RatBall := localContactBall tau2405 center2405
def work2405 : RoundedTauEval :=
  evalTau precision tau2405 contact2405 logTwoBall

theorem center_sq2405 : (center2405.re : ℝ)^2 +
    (center2405.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2405]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2405 : work2405.theta.ok = true ∧
    work2405.jac.invOK = true ∧ acceptsUnitSq work2405.out = true := by decide +kernel

def cell2405 : CellCertificate where
  tauBall := tau2405
  contactCenter := center2405
  contactBall := contact2405
  work := work2405
  center_sq := center_sq2405
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2405.1
  jac_ok := checks2405.2.1
  accepted := checks2405.2.2

def tau2406 : RatBall :=
  ⟨⟨33/320, 117/320⟩, 3/640⟩
def center2406 : GaussianRat :=
  ⟨1648401/20000000, 65635667/250000000⟩
def contact2406 : RatBall := localContactBall tau2406 center2406
def work2406 : RoundedTauEval :=
  evalTau precision tau2406 contact2406 logTwoBall

theorem center_sq2406 : (center2406.re : ℝ)^2 +
    (center2406.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2406]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2406 : work2406.theta.ok = true ∧
    work2406.jac.invOK = true ∧ acceptsUnitSq work2406.out = true := by decide +kernel

def cell2406 : CellCertificate where
  tauBall := tau2406
  contactCenter := center2406
  contactBall := contact2406
  work := work2406
  center_sq := center_sq2406
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2406.1
  jac_ok := checks2406.2.1
  accepted := checks2406.2.2

def tau2407 : RatBall :=
  ⟨⟨7/64, 117/320⟩, 3/640⟩
def center2407 : GaussianRat :=
  ⟨43670547/500000000, 65522293/250000000⟩
def contact2407 : RatBall := localContactBall tau2407 center2407
def work2407 : RoundedTauEval :=
  evalTau precision tau2407 contact2407 logTwoBall

theorem center_sq2407 : (center2407.re : ℝ)^2 +
    (center2407.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2407]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2407 : work2407.theta.ok = true ∧
    work2407.jac.invOK = true ∧ acceptsUnitSq work2407.out = true := by decide +kernel

def cell2407 : CellCertificate where
  tauBall := tau2407
  contactCenter := center2407
  contactBall := contact2407
  work := work2407
  center_sq := center_sq2407
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2407.1
  jac_ok := checks2407.2.1
  accepted := checks2407.2.2

def cells : List CellCertificate := [cell2400, cell2401, cell2402, cell2403, cell2404, cell2405, cell2406, cell2407]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0300

end


