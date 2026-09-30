-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0302
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0302
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:42:19.414138+00:00
-- url     : https://prove2.me/theorems/9755ae47-2ea0-4db8-b929-bcde96b8cf60
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0302` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0302` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0302` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0302 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0302.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0302 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0302

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2416 : RatBall :=
  ⟨⟨9/64, 23/64⟩, 3/640⟩
def center2416 : GaussianRat :=
  ⟨889321/8000000, 254626433/1000000000⟩
def contact2416 : RatBall := localContactBall tau2416 center2416
def work2416 : RoundedTauEval :=
  evalTau precision tau2416 contact2416 logTwoBall

theorem center_sq2416 : (center2416.re : ℝ)^2 +
    (center2416.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2416]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2416 : work2416.theta.ok = true ∧
    work2416.jac.invOK = true ∧ acceptsUnitSq work2416.out = true := by decide +kernel

def cell2416 : CellCertificate where
  tauBall := tau2416
  contactCenter := center2416
  contactBall := contact2416
  work := work2416
  center_sq := center_sq2416
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2416.1
  jac_ok := checks2416.2.1
  accepted := checks2416.2.2

def tau2417 : RatBall :=
  ⟨⟨49/320, 113/320⟩, 3/640⟩
def center2417 : GaussianRat :=
  ⟨120169401/1000000000, 248665661/1000000000⟩
def contact2417 : RatBall := localContactBall tau2417 center2417
def work2417 : RoundedTauEval :=
  evalTau precision tau2417 contact2417 logTwoBall

theorem center_sq2417 : (center2417.re : ℝ)^2 +
    (center2417.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2417]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2417 : work2417.theta.ok = true ∧
    work2417.jac.invOK = true ∧ acceptsUnitSq work2417.out = true := by decide +kernel

def cell2417 : CellCertificate where
  tauBall := tau2417
  contactCenter := center2417
  contactBall := contact2417
  work := work2417
  center_sq := center_sq2417
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2417.1
  jac_ok := checks2417.2.1
  accepted := checks2417.2.2

def tau2418 : RatBall :=
  ⟨⟨51/320, 113/320⟩, 3/640⟩
def center2418 : GaussianRat :=
  ⟨124928411/1000000000, 12402911/50000000⟩
def contact2418 : RatBall := localContactBall tau2418 center2418
def work2418 : RoundedTauEval :=
  evalTau precision tau2418 contact2418 logTwoBall

theorem center_sq2418 : (center2418.re : ℝ)^2 +
    (center2418.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2418]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2418 : work2418.theta.ok = true ∧
    work2418.jac.invOK = true ∧ acceptsUnitSq work2418.out = true := by decide +kernel

def cell2418 : CellCertificate where
  tauBall := tau2418
  contactCenter := center2418
  contactBall := contact2418
  work := work2418
  center_sq := center_sq2418
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2418.1
  jac_ok := checks2418.2.1
  accepted := checks2418.2.2

def tau2419 : RatBall :=
  ⟨⟨53/320, 113/320⟩, 3/640⟩
def center2419 : GaussianRat :=
  ⟨129670733/1000000000, 15464381/62500000⟩
def contact2419 : RatBall := localContactBall tau2419 center2419
def work2419 : RoundedTauEval :=
  evalTau precision tau2419 contact2419 logTwoBall

theorem center_sq2419 : (center2419.re : ℝ)^2 +
    (center2419.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2419]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2419 : work2419.theta.ok = true ∧
    work2419.jac.invOK = true ∧ acceptsUnitSq work2419.out = true := by decide +kernel

def cell2419 : CellCertificate where
  tauBall := tau2419
  contactCenter := center2419
  contactBall := contact2419
  work := work2419
  center_sq := center_sq2419
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2419.1
  jac_ok := checks2419.2.1
  accepted := checks2419.2.2

def tau2420 : RatBall :=
  ⟨⟨93/320, 77/320⟩, 3/640⟩
def center2420 : GaussianRat :=
  ⟨12912721/62500000, 7762627/50000000⟩
def contact2420 : RatBall := localContactBall tau2420 center2420
def work2420 : RoundedTauEval :=
  evalTau precision tau2420 contact2420 logTwoBall

theorem center_sq2420 : (center2420.re : ℝ)^2 +
    (center2420.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2420]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2420 : work2420.theta.ok = true ∧
    work2420.jac.invOK = true ∧ acceptsUnitSq work2420.out = true := by decide +kernel

def cell2420 : CellCertificate where
  tauBall := tau2420
  contactCenter := center2420
  contactBall := contact2420
  work := work2420
  center_sq := center_sq2420
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2420.1
  jac_ok := checks2420.2.1
  accepted := checks2420.2.2

def tau2421 : RatBall :=
  ⟨⟨19/64, 77/320⟩, 3/640⟩
def center2421 : GaussianRat :=
  ⟨26341087/125000000, 77331419/500000000⟩
def contact2421 : RatBall := localContactBall tau2421 center2421
def work2421 : RoundedTauEval :=
  evalTau precision tau2421 contact2421 logTwoBall

theorem center_sq2421 : (center2421.re : ℝ)^2 +
    (center2421.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2421]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2421 : work2421.theta.ok = true ∧
    work2421.jac.invOK = true ∧ acceptsUnitSq work2421.out = true := by decide +kernel

def cell2421 : CellCertificate where
  tauBall := tau2421
  contactCenter := center2421
  contactBall := contact2421
  work := work2421
  center_sq := center_sq2421
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2421.1
  jac_ok := checks2421.2.1
  accepted := checks2421.2.2

def tau2422 : RatBall :=
  ⟨⟨93/320, 79/320⟩, 3/640⟩
def center2422 : GaussianRat :=
  ⟨207198371/1000000000, 15939079/100000000⟩
def contact2422 : RatBall := localContactBall tau2422 center2422
def work2422 : RoundedTauEval :=
  evalTau precision tau2422 contact2422 logTwoBall

theorem center_sq2422 : (center2422.re : ℝ)^2 +
    (center2422.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2422]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2422 : work2422.theta.ok = true ∧
    work2422.jac.invOK = true ∧ acceptsUnitSq work2422.out = true := by decide +kernel

def cell2422 : CellCertificate where
  tauBall := tau2422
  contactCenter := center2422
  contactBall := contact2422
  work := work2422
  center_sq := center_sq2422
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2422.1
  jac_ok := checks2422.2.1
  accepted := checks2422.2.2

def tau2423 : RatBall :=
  ⟨⟨19/64, 79/320⟩, 3/640⟩
def center2423 : GaussianRat :=
  ⟨211331481/1000000000, 158782791/1000000000⟩
def contact2423 : RatBall := localContactBall tau2423 center2423
def work2423 : RoundedTauEval :=
  evalTau precision tau2423 contact2423 logTwoBall

theorem center_sq2423 : (center2423.re : ℝ)^2 +
    (center2423.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2423]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2423 : work2423.theta.ok = true ∧
    work2423.jac.invOK = true ∧ acceptsUnitSq work2423.out = true := by decide +kernel

def cell2423 : CellCertificate where
  tauBall := tau2423
  contactCenter := center2423
  contactBall := contact2423
  work := work2423
  center_sq := center_sq2423
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2423.1
  jac_ok := checks2423.2.1
  accepted := checks2423.2.2

def cells : List CellCertificate := [cell2416, cell2417, cell2418, cell2419, cell2420, cell2421, cell2422, cell2423]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0302

end


