-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0269_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0269_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:33:11.709336+00:00
-- url     : https://prove2.me/theorems/9dd77933-aaa7-4ddd-a761-f001e0ba09c2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0269 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0269 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0269 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0269 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0269 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0269

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2152 : RatBall :=
  ⟨⟨-5/64, 113/320⟩, 3/640⟩
def center2152 : GaussianRat :=
  ⟨-61962339/1000000000, 63553661/250000000⟩
def contact2152 : RatBall := localContactBall tau2152 center2152
def work2152 : RoundedTauEval :=
  evalTau precision tau2152 contact2152 logTwoBall

theorem center_sq2152 : (center2152.re : ℝ)^2 +
    (center2152.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2152]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2152 : work2152.theta.ok = true ∧
    work2152.jac.invOK = true ∧ acceptsUnitSq work2152.out = true := by decide +kernel

def cell2152 : CellCertificate where
  tauBall := tau2152
  contactCenter := center2152
  contactBall := contact2152
  work := work2152
  center_sq := center_sq2152
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2152.1
  jac_ok := checks2152.2.1
  accepted := checks2152.2.2

def tau2153 : RatBall :=
  ⟨⟨-27/320, 23/64⟩, 3/640⟩
def center2153 : GaussianRat :=
  ⟨-67227179/1000000000, 258804339/1000000000⟩
def contact2153 : RatBall := localContactBall tau2153 center2153
def work2153 : RoundedTauEval :=
  evalTau precision tau2153 contact2153 logTwoBall

theorem center_sq2153 : (center2153.re : ℝ)^2 +
    (center2153.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2153]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2153 : work2153.theta.ok = true ∧
    work2153.jac.invOK = true ∧ acceptsUnitSq work2153.out = true := by decide +kernel

def cell2153 : CellCertificate where
  tauBall := tau2153
  contactCenter := center2153
  contactBall := contact2153
  work := work2153
  center_sq := center_sq2153
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2153.1
  jac_ok := checks2153.2.1
  accepted := checks2153.2.2

def tau2154 : RatBall :=
  ⟨⟨-5/64, 23/64⟩, 3/640⟩
def center2154 : GaussianRat :=
  ⟨-15571843/250000000, 51829311/200000000⟩
def contact2154 : RatBall := localContactBall tau2154 center2154
def work2154 : RoundedTauEval :=
  evalTau precision tau2154 contact2154 logTwoBall

theorem center_sq2154 : (center2154.re : ℝ)^2 +
    (center2154.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2154]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2154 : work2154.theta.ok = true ∧
    work2154.jac.invOK = true ∧ acceptsUnitSq work2154.out = true := by decide +kernel

def cell2154 : CellCertificate where
  tauBall := tau2154
  contactCenter := center2154
  contactBall := contact2154
  work := work2154
  center_sq := center_sq2154
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2154.1
  jac_ok := checks2154.2.1
  accepted := checks2154.2.2

def tau2155 : RatBall :=
  ⟨⟨-31/320, 117/320⟩, 3/640⟩
def center2155 : GaussianRat :=
  ⟨-774869/10000000, 65742793/250000000⟩
def contact2155 : RatBall := localContactBall tau2155 center2155
def work2155 : RoundedTauEval :=
  evalTau precision tau2155 contact2155 logTwoBall

theorem center_sq2155 : (center2155.re : ℝ)^2 +
    (center2155.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2155]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2155 : work2155.theta.ok = true ∧
    work2155.jac.invOK = true ∧ acceptsUnitSq work2155.out = true := by decide +kernel

def cell2155 : CellCertificate where
  tauBall := tau2155
  contactCenter := center2155
  contactBall := contact2155
  work := work2155
  center_sq := center_sq2155
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2155.1
  jac_ok := checks2155.2.1
  accepted := checks2155.2.2

def tau2156 : RatBall :=
  ⟨⟨-29/320, 117/320⟩, 3/640⟩
def center2156 : GaussianRat :=
  ⟨-7254231/100000000, 263374389/1000000000⟩
def contact2156 : RatBall := localContactBall tau2156 center2156
def work2156 : RoundedTauEval :=
  evalTau precision tau2156 contact2156 logTwoBall

theorem center_sq2156 : (center2156.re : ℝ)^2 +
    (center2156.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2156]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2156 : work2156.theta.ok = true ∧
    work2156.jac.invOK = true ∧ acceptsUnitSq work2156.out = true := by decide +kernel

def cell2156 : CellCertificate where
  tauBall := tau2156
  contactCenter := center2156
  contactBall := contact2156
  work := work2156
  center_sq := center_sq2156
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2156.1
  jac_ok := checks2156.2.1
  accepted := checks2156.2.2

def tau2157 : RatBall :=
  ⟨⟨-31/320, 119/320⟩, 3/640⟩
def center2157 : GaussianRat :=
  ⟨-77908577/1000000000, 267922911/1000000000⟩
def contact2157 : RatBall := localContactBall tau2157 center2157
def work2157 : RoundedTauEval :=
  evalTau precision tau2157 contact2157 logTwoBall

theorem center_sq2157 : (center2157.re : ℝ)^2 +
    (center2157.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2157]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2157 : work2157.theta.ok = true ∧
    work2157.jac.invOK = true ∧ acceptsUnitSq work2157.out = true := by decide +kernel

def cell2157 : CellCertificate where
  tauBall := tau2157
  contactCenter := center2157
  contactBall := contact2157
  work := work2157
  center_sq := center_sq2157
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2157.1
  jac_ok := checks2157.2.1
  accepted := checks2157.2.2

def tau2158 : RatBall :=
  ⟨⟨-29/320, 119/320⟩, 3/640⟩
def center2158 : GaussianRat :=
  ⟨-14587643/200000000, 268337373/1000000000⟩
def contact2158 : RatBall := localContactBall tau2158 center2158
def work2158 : RoundedTauEval :=
  evalTau precision tau2158 contact2158 logTwoBall

theorem center_sq2158 : (center2158.re : ℝ)^2 +
    (center2158.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2158]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2158 : work2158.theta.ok = true ∧
    work2158.jac.invOK = true ∧ acceptsUnitSq work2158.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0269


