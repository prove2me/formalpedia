-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0286
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0286
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:19:15.390904+00:00
-- url     : https://prove2.me/theorems/be13bd6b-9962-441d-9df1-a174063d3216
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0286` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0286` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0286` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0286 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0286.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0286 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0286

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2288 : RatBall :=
  ⟨⟨19/320, 119/320⟩, 3/640⟩
def center2288 : GaussianRat :=
  ⟨47935117/1000000000, 2109457/7812500⟩
def contact2288 : RatBall := localContactBall tau2288 center2288
def work2288 : RoundedTauEval :=
  evalTau precision tau2288 contact2288 logTwoBall

theorem center_sq2288 : (center2288.re : ℝ)^2 +
    (center2288.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2288]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2288 : work2288.theta.ok = true ∧
    work2288.jac.invOK = true ∧ acceptsUnitSq work2288.out = true := by decide +kernel

def cell2288 : CellCertificate where
  tauBall := tau2288
  contactCenter := center2288
  contactBall := contact2288
  work := work2288
  center_sq := center_sq2288
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2288.1
  jac_ok := checks2288.2.1
  accepted := checks2288.2.2

def tau2289 : RatBall :=
  ⟨⟨21/320, 117/320⟩, 3/640⟩
def center2289 : GaussianRat :=
  ⟨52663303/1000000000, 52945801/200000000⟩
def contact2289 : RatBall := localContactBall tau2289 center2289
def work2289 : RoundedTauEval :=
  evalTau precision tau2289 contact2289 logTwoBall

theorem center_sq2289 : (center2289.re : ℝ)^2 +
    (center2289.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2289]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2289 : work2289.theta.ok = true ∧
    work2289.jac.invOK = true ∧ acceptsUnitSq work2289.out = true := by decide +kernel

def cell2289 : CellCertificate where
  tauBall := tau2289
  contactCenter := center2289
  contactBall := contact2289
  work := work2289
  center_sq := center_sq2289
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2289.1
  jac_ok := checks2289.2.1
  accepted := checks2289.2.2

def tau2290 : RatBall :=
  ⟨⟨23/320, 117/320⟩, 3/640⟩
def center2290 : GaussianRat :=
  ⟨57646751/1000000000, 52885917/200000000⟩
def contact2290 : RatBall := localContactBall tau2290 center2290
def work2290 : RoundedTauEval :=
  evalTau precision tau2290 contact2290 logTwoBall

theorem center_sq2290 : (center2290.re : ℝ)^2 +
    (center2290.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2290]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2290 : work2290.theta.ok = true ∧
    work2290.jac.invOK = true ∧ acceptsUnitSq work2290.out = true := by decide +kernel

def cell2290 : CellCertificate where
  tauBall := tau2290
  contactCenter := center2290
  contactBall := contact2290
  work := work2290
  center_sq := center_sq2290
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2290.1
  jac_ok := checks2290.2.1
  accepted := checks2290.2.2

def tau2291 : RatBall :=
  ⟨⟨21/320, 119/320⟩, 3/640⟩
def center2291 : GaussianRat :=
  ⟨26476749/500000000, 33716241/125000000⟩
def contact2291 : RatBall := localContactBall tau2291 center2291
def work2291 : RoundedTauEval :=
  evalTau precision tau2291 contact2291 logTwoBall

theorem center_sq2291 : (center2291.re : ℝ)^2 +
    (center2291.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2291]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2291 : work2291.theta.ok = true ∧
    work2291.jac.invOK = true ∧ acceptsUnitSq work2291.out = true := by decide +kernel

def cell2291 : CellCertificate where
  tauBall := tau2291
  contactCenter := center2291
  contactBall := contact2291
  work := work2291
  center_sq := center_sq2291
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2291.1
  jac_ok := checks2291.2.1
  accepted := checks2291.2.2

def tau2292 : RatBall :=
  ⟨⟨23/320, 119/320⟩, 3/640⟩
def center2292 : GaussianRat :=
  ⟨14490933/250000000, 269422101/1000000000⟩
def contact2292 : RatBall := localContactBall tau2292 center2292
def work2292 : RoundedTauEval :=
  evalTau precision tau2292 contact2292 logTwoBall

theorem center_sq2292 : (center2292.re : ℝ)^2 +
    (center2292.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2292]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2292 : work2292.theta.ok = true ∧
    work2292.jac.invOK = true ∧ acceptsUnitSq work2292.out = true := by decide +kernel

def cell2292 : CellCertificate where
  tauBall := tau2292
  contactCenter := center2292
  contactBall := contact2292
  work := work2292
  center_sq := center_sq2292
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2292.1
  jac_ok := checks2292.2.1
  accepted := checks2292.2.2

def tau2293 : RatBall :=
  ⟨⟨5/64, 113/320⟩, 3/640⟩
def center2293 : GaussianRat :=
  ⟨61962339/1000000000, 63553661/250000000⟩
def contact2293 : RatBall := localContactBall tau2293 center2293
def work2293 : RoundedTauEval :=
  evalTau precision tau2293 contact2293 logTwoBall

theorem center_sq2293 : (center2293.re : ℝ)^2 +
    (center2293.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2293]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2293 : work2293.theta.ok = true ∧
    work2293.jac.invOK = true ∧ acceptsUnitSq work2293.out = true := by decide +kernel

def cell2293 : CellCertificate where
  tauBall := tau2293
  contactCenter := center2293
  contactBall := contact2293
  work := work2293
  center_sq := center_sq2293
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2293.1
  jac_ok := checks2293.2.1
  accepted := checks2293.2.2

def tau2294 : RatBall :=
  ⟨⟨27/320, 113/320⟩, 3/640⟩
def center2294 : GaussianRat :=
  ⟨33438609/500000000, 253881789/1000000000⟩
def contact2294 : RatBall := localContactBall tau2294 center2294
def work2294 : RoundedTauEval :=
  evalTau precision tau2294 contact2294 logTwoBall

theorem center_sq2294 : (center2294.re : ℝ)^2 +
    (center2294.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2294]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2294 : work2294.theta.ok = true ∧
    work2294.jac.invOK = true ∧ acceptsUnitSq work2294.out = true := by decide +kernel

def cell2294 : CellCertificate where
  tauBall := tau2294
  contactCenter := center2294
  contactBall := contact2294
  work := work2294
  center_sq := center_sq2294
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2294.1
  jac_ok := checks2294.2.1
  accepted := checks2294.2.2

def tau2295 : RatBall :=
  ⟨⟨5/64, 23/64⟩, 3/640⟩
def center2295 : GaussianRat :=
  ⟨15571843/250000000, 51829311/200000000⟩
def contact2295 : RatBall := localContactBall tau2295 center2295
def work2295 : RoundedTauEval :=
  evalTau precision tau2295 contact2295 logTwoBall

theorem center_sq2295 : (center2295.re : ℝ)^2 +
    (center2295.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2295]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2295 : work2295.theta.ok = true ∧
    work2295.jac.invOK = true ∧ acceptsUnitSq work2295.out = true := by decide +kernel

def cell2295 : CellCertificate where
  tauBall := tau2295
  contactCenter := center2295
  contactBall := contact2295
  work := work2295
  center_sq := center_sq2295
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2295.1
  jac_ok := checks2295.2.1
  accepted := checks2295.2.2

def cells : List CellCertificate := [cell2288, cell2289, cell2290, cell2291, cell2292, cell2293, cell2294, cell2295]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0286

end


