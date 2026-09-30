-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0299
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0299
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:31:16.837996+00:00
-- url     : https://prove2.me/theorems/b1e03fe8-e113-4ff6-9853-385eb717924c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0299` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0299` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0299` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0299 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0299.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0299 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0299

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2392 : RatBall :=
  ⟨⟨57/320, 109/320⟩, 3/640⟩
def center2392 : GaussianRat :=
  ⟨137782813/1000000000, 5918871/25000000⟩
def contact2392 : RatBall := localContactBall tau2392 center2392
def work2392 : RoundedTauEval :=
  evalTau precision tau2392 contact2392 logTwoBall

theorem center_sq2392 : (center2392.re : ℝ)^2 +
    (center2392.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2392]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2392 : work2392.theta.ok = true ∧
    work2392.jac.invOK = true ∧ acceptsUnitSq work2392.out = true := by decide +kernel

def cell2392 : CellCertificate where
  tauBall := tau2392
  contactCenter := center2392
  contactBall := contact2392
  work := work2392
  center_sq := center_sq2392
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2392.1
  jac_ok := checks2392.2.1
  accepted := checks2392.2.2

def tau2393 : RatBall :=
  ⟨⟨59/320, 109/320⟩, 3/640⟩
def center2393 : GaussianRat :=
  ⟨71217211/500000000, 236102993/1000000000⟩
def contact2393 : RatBall := localContactBall tau2393 center2393
def work2393 : RoundedTauEval :=
  evalTau precision tau2393 contact2393 logTwoBall

theorem center_sq2393 : (center2393.re : ℝ)^2 +
    (center2393.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2393]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2393 : work2393.theta.ok = true ∧
    work2393.jac.invOK = true ∧ acceptsUnitSq work2393.out = true := by decide +kernel

def cell2393 : CellCertificate where
  tauBall := tau2393
  contactCenter := center2393
  contactBall := contact2393
  work := work2393
  center_sq := center_sq2393
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2393.1
  jac_ok := checks2393.2.1
  accepted := checks2393.2.2

def tau2394 : RatBall :=
  ⟨⟨57/320, 111/320⟩, 3/640⟩
def center2394 : GaussianRat :=
  ⟨138434183/1000000000, 120712289/500000000⟩
def contact2394 : RatBall := localContactBall tau2394 center2394
def work2394 : RoundedTauEval :=
  evalTau precision tau2394 contact2394 logTwoBall

theorem center_sq2394 : (center2394.re : ℝ)^2 +
    (center2394.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2394]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2394 : work2394.theta.ok = true ∧
    work2394.jac.invOK = true ∧ acceptsUnitSq work2394.out = true := by decide +kernel

def cell2394 : CellCertificate where
  tauBall := tau2394
  contactCenter := center2394
  contactBall := contact2394
  work := work2394
  center_sq := center_sq2394
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2394.1
  jac_ok := checks2394.2.1
  accepted := checks2394.2.2

def tau2395 : RatBall :=
  ⟨⟨59/320, 111/320⟩, 3/640⟩
def center2395 : GaussianRat :=
  ⟨143104409/1000000000, 240754941/1000000000⟩
def contact2395 : RatBall := localContactBall tau2395 center2395
def work2395 : RoundedTauEval :=
  evalTau precision tau2395 contact2395 logTwoBall

theorem center_sq2395 : (center2395.re : ℝ)^2 +
    (center2395.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2395]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2395 : work2395.theta.ok = true ∧
    work2395.jac.invOK = true ∧ acceptsUnitSq work2395.out = true := by decide +kernel

def cell2395 : CellCertificate where
  tauBall := tau2395
  contactCenter := center2395
  contactBall := contact2395
  work := work2395
  center_sq := center_sq2395
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2395.1
  jac_ok := checks2395.2.1
  accepted := checks2395.2.2

def tau2396 : RatBall :=
  ⟨⟨61/320, 109/320⟩, 3/640⟩
def center2396 : GaussianRat :=
  ⟨147068213/1000000000, 14714559/62500000⟩
def contact2396 : RatBall := localContactBall tau2396 center2396
def work2396 : RoundedTauEval :=
  evalTau precision tau2396 contact2396 logTwoBall

theorem center_sq2396 : (center2396.re : ℝ)^2 +
    (center2396.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2396]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2396 : work2396.theta.ok = true ∧
    work2396.jac.invOK = true ∧ acceptsUnitSq work2396.out = true := by decide +kernel

def cell2396 : CellCertificate where
  tauBall := tau2396
  contactCenter := center2396
  contactBall := contact2396
  work := work2396
  center_sq := center_sq2396
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2396.1
  jac_ok := checks2396.2.1
  accepted := checks2396.2.2

def tau2397 : RatBall :=
  ⟨⟨63/320, 109/320⟩, 3/640⟩
def center2397 : GaussianRat :=
  ⟨75841877/500000000, 234745077/1000000000⟩
def contact2397 : RatBall := localContactBall tau2397 center2397
def work2397 : RoundedTauEval :=
  evalTau precision tau2397 contact2397 logTwoBall

theorem center_sq2397 : (center2397.re : ℝ)^2 +
    (center2397.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2397]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2397 : work2397.theta.ok = true ∧
    work2397.jac.invOK = true ∧ acceptsUnitSq work2397.out = true := by decide +kernel

def cell2397 : CellCertificate where
  tauBall := tau2397
  contactCenter := center2397
  contactBall := contact2397
  work := work2397
  center_sq := center_sq2397
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2397.1
  jac_ok := checks2397.2.1
  accepted := checks2397.2.2

def tau2398 : RatBall :=
  ⟨⟨33/320, 113/320⟩, 3/640⟩
def center2398 : GaussianRat :=
  ⟨16312353/200000000, 252737367/1000000000⟩
def contact2398 : RatBall := localContactBall tau2398 center2398
def work2398 : RoundedTauEval :=
  evalTau precision tau2398 contact2398 logTwoBall

theorem center_sq2398 : (center2398.re : ℝ)^2 +
    (center2398.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2398]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2398 : work2398.theta.ok = true ∧
    work2398.jac.invOK = true ∧ acceptsUnitSq work2398.out = true := by decide +kernel

def cell2398 : CellCertificate where
  tauBall := tau2398
  contactCenter := center2398
  contactBall := contact2398
  work := work2398
  center_sq := center_sq2398
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2398.1
  jac_ok := checks2398.2.1
  accepted := checks2398.2.2

def tau2399 : RatBall :=
  ⟨⟨7/64, 113/320⟩, 3/640⟩
def center2399 : GaussianRat :=
  ⟨86434423/1000000000, 50461627/200000000⟩
def contact2399 : RatBall := localContactBall tau2399 center2399
def work2399 : RoundedTauEval :=
  evalTau precision tau2399 contact2399 logTwoBall

theorem center_sq2399 : (center2399.re : ℝ)^2 +
    (center2399.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2399]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2399 : work2399.theta.ok = true ∧
    work2399.jac.invOK = true ∧ acceptsUnitSq work2399.out = true := by decide +kernel

def cell2399 : CellCertificate where
  tauBall := tau2399
  contactCenter := center2399
  contactBall := contact2399
  work := work2399
  center_sq := center_sq2399
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2399.1
  jac_ok := checks2399.2.1
  accepted := checks2399.2.2

def cells : List CellCertificate := [cell2392, cell2393, cell2394, cell2395, cell2396, cell2397, cell2398, cell2399]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0299

end


