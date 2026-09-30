-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0274_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0274_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:14:16.048044+00:00
-- url     : https://prove2.me/theorems/b7156c75-c80d-4aaf-a3b7-fc99935b3710
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0274 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2192 : RatBall :=
  ⟨⟨-3/64, 119/320⟩, 3/640⟩
def center2192 : GaussianRat :=
  ⟨-18938457/500000000, 5409781/20000000⟩
def contact2192 : RatBall := localContactBall tau2192 center2192
def work2192 : RoundedTauEval :=
  evalTau precision tau2192 contact2192 logTwoBall

theorem center_sq2192 : (center2192.re : ℝ)^2 +
    (center2192.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2192 : work2192.theta.ok = true ∧
    work2192.jac.invOK = true ∧ acceptsUnitSq work2192.out = true := by decide +kernel

def cell2192 : CellCertificate where
  tauBall := tau2192
  contactCenter := center2192
  contactBall := contact2192
  work := work2192
  center_sq := center_sq2192
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2192.1
  jac_ok := checks2192.2.1
  accepted := checks2192.2.2

def tau2193 : RatBall :=
  ⟨⟨-13/320, 119/320⟩, 3/640⟩
def center2193 : GaussianRat :=
  ⟨-32838611/1000000000, 135343343/500000000⟩
def contact2193 : RatBall := localContactBall tau2193 center2193
def work2193 : RoundedTauEval :=
  evalTau precision tau2193 contact2193 logTwoBall

theorem center_sq2193 : (center2193.re : ℝ)^2 +
    (center2193.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2193]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2193 : work2193.theta.ok = true ∧
    work2193.jac.invOK = true ∧ acceptsUnitSq work2193.out = true := by decide +kernel

def cell2193 : CellCertificate where
  tauBall := tau2193
  contactCenter := center2193
  contactBall := contact2193
  work := work2193
  center_sq := center_sq2193
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2193.1
  jac_ok := checks2193.2.1
  accepted := checks2193.2.2

def tau2194 : RatBall :=
  ⟨⟨-11/320, 117/320⟩, 3/640⟩
def center2194 : GaussianRat :=
  ⟨-863803/31250000, 33228071/125000000⟩
def contact2194 : RatBall := localContactBall tau2194 center2194
def work2194 : RoundedTauEval :=
  evalTau precision tau2194 contact2194 logTwoBall

theorem center_sq2194 : (center2194.re : ℝ)^2 +
    (center2194.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2194]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2194 : work2194.theta.ok = true ∧
    work2194.jac.invOK = true ∧ acceptsUnitSq work2194.out = true := by decide +kernel

def cell2194 : CellCertificate where
  tauBall := tau2194
  contactCenter := center2194
  contactBall := contact2194
  work := work2194
  center_sq := center_sq2194
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2194.1
  jac_ok := checks2194.2.1
  accepted := checks2194.2.2

def tau2195 : RatBall :=
  ⟨⟨-9/320, 117/320⟩, 3/640⟩
def center2195 : GaussianRat :=
  ⟨-4524341/200000000, 53192453/200000000⟩
def contact2195 : RatBall := localContactBall tau2195 center2195
def work2195 : RoundedTauEval :=
  evalTau precision tau2195 contact2195 logTwoBall

theorem center_sq2195 : (center2195.re : ℝ)^2 +
    (center2195.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2195]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2195 : work2195.theta.ok = true ∧
    work2195.jac.invOK = true ∧ acceptsUnitSq work2195.out = true := by decide +kernel

def cell2195 : CellCertificate where
  tauBall := tau2195
  contactCenter := center2195
  contactBall := contact2195
  work := work2195
  center_sq := center_sq2195
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2195.1
  jac_ok := checks2195.2.1
  accepted := checks2195.2.2

def tau2196 : RatBall :=
  ⟨⟨-11/320, 119/320⟩, 3/640⟩
def center2196 : GaussianRat :=
  ⟨-27795199/1000000000, 135428181/500000000⟩
def contact2196 : RatBall := localContactBall tau2196 center2196
def work2196 : RoundedTauEval :=
  evalTau precision tau2196 contact2196 logTwoBall

theorem center_sq2196 : (center2196.re : ℝ)^2 +
    (center2196.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2196]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2196 : work2196.theta.ok = true ∧
    work2196.jac.invOK = true ∧ acceptsUnitSq work2196.out = true := by decide +kernel

def cell2196 : CellCertificate where
  tauBall := tau2196
  contactCenter := center2196
  contactBall := contact2196
  work := work2196
  center_sq := center_sq2196
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2196.1
  jac_ok := checks2196.2.1
  accepted := checks2196.2.2

def tau2197 : RatBall :=
  ⟨⟨-9/320, 119/320⟩, 3/640⟩
def center2197 : GaussianRat :=
  ⟨-22747453/1000000000, 270997951/1000000000⟩
def contact2197 : RatBall := localContactBall tau2197 center2197
def work2197 : RoundedTauEval :=
  evalTau precision tau2197 contact2197 logTwoBall

theorem center_sq2197 : (center2197.re : ℝ)^2 +
    (center2197.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2197]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274


