-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0270
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0270
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:32:40.342168+00:00
-- url     : https://prove2.me/theorems/e6a384a8-3469-4df3-983b-6845ea275b33
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0270.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0270_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2164 : (center2164.re : ℝ)^2 +
    (center2164.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2164]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2164 : work2164.theta.ok = true ∧
    work2164.jac.invOK = true ∧ acceptsUnitSq work2164.out = true := by decide +kernel

def cell2164 : CellCertificate where
  tauBall := tau2164
  contactCenter := center2164
  contactBall := contact2164
  work := work2164
  center_sq := center_sq2164
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2164.1
  jac_ok := checks2164.2.1
  accepted := checks2164.2.2

def tau2165 : RatBall :=
  ⟨⟨-23/320, 23/64⟩, 3/640⟩
def center2165 : GaussianRat :=
  ⟨-5733843/100000000, 129731693/500000000⟩
def contact2165 : RatBall := localContactBall tau2165 center2165
def work2165 : RoundedTauEval :=
  evalTau precision tau2165 contact2165 logTwoBall

theorem center_sq2165 : (center2165.re : ℝ)^2 +
    (center2165.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2165]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2165 : work2165.theta.ok = true ∧
    work2165.jac.invOK = true ∧ acceptsUnitSq work2165.out = true := by decide +kernel

def cell2165 : CellCertificate where
  tauBall := tau2165
  contactCenter := center2165
  contactBall := contact2165
  work := work2165
  center_sq := center_sq2165
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2165.1
  jac_ok := checks2165.2.1
  accepted := checks2165.2.2

def tau2166 : RatBall :=
  ⟨⟨-21/320, 23/64⟩, 3/640⟩
def center2166 : GaussianRat :=
  ⟨-6547631/125000000, 64938653/250000000⟩
def contact2166 : RatBall := localContactBall tau2166 center2166
def work2166 : RoundedTauEval :=
  evalTau precision tau2166 contact2166 logTwoBall

theorem center_sq2166 : (center2166.re : ℝ)^2 +
    (center2166.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2166]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2166 : work2166.theta.ok = true ∧
    work2166.jac.invOK = true ∧ acceptsUnitSq work2166.out = true := by decide +kernel

def cell2166 : CellCertificate where
  tauBall := tau2166
  contactCenter := center2166
  contactBall := contact2166
  work := work2166
  center_sq := center_sq2166
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2166.1
  jac_ok := checks2166.2.1
  accepted := checks2166.2.2

def tau2167 : RatBall :=
  ⟨⟨-19/320, 113/320⟩, 3/640⟩
def center2167 : GaussianRat :=
  ⟨-47166967/1000000000, 255064157/1000000000⟩
def contact2167 : RatBall := localContactBall tau2167 center2167
def work2167 : RoundedTauEval :=
  evalTau precision tau2167 contact2167 logTwoBall

theorem center_sq2167 : (center2167.re : ℝ)^2 +
    (center2167.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2167]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2167 : work2167.theta.ok = true ∧
    work2167.jac.invOK = true ∧ acceptsUnitSq work2167.out = true := by decide +kernel

def cell2167 : CellCertificate where
  tauBall := tau2167
  contactCenter := center2167
  contactBall := contact2167
  work := work2167
  center_sq := center_sq2167
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2167.1
  jac_ok := checks2167.2.1
  accepted := checks2167.2.2

def cells : List CellCertificate := [cell2160, cell2161, cell2162, cell2163, cell2164, cell2165, cell2166, cell2167]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270


