-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0271_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0271_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:22:24.375089+00:00
-- url     : https://prove2.me/theorems/876401b6-cd29-4adc-ac33-0854975448dd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0271 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0271 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0271 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0271 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0271 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0271

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2168 : RatBall :=
  ⟨⟨-17/320, 113/320⟩, 3/640⟩
def center2168 : GaussianRat :=
  ⟨-42220551/1000000000, 25529699/100000000⟩
def contact2168 : RatBall := localContactBall tau2168 center2168
def work2168 : RoundedTauEval :=
  evalTau precision tau2168 contact2168 logTwoBall

theorem center_sq2168 : (center2168.re : ℝ)^2 +
    (center2168.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2168]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2168 : work2168.theta.ok = true ∧
    work2168.jac.invOK = true ∧ acceptsUnitSq work2168.out = true := by decide +kernel

def cell2168 : CellCertificate where
  tauBall := tau2168
  contactCenter := center2168
  contactBall := contact2168
  work := work2168
  center_sq := center_sq2168
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2168.1
  jac_ok := checks2168.2.1
  accepted := checks2168.2.2

def tau2169 : RatBall :=
  ⟨⟨-19/320, 23/64⟩, 3/640⟩
def center2169 : GaussianRat :=
  ⟨-47415929/1000000000, 260020027/1000000000⟩
def contact2169 : RatBall := localContactBall tau2169 center2169
def work2169 : RoundedTauEval :=
  evalTau precision tau2169 contact2169 logTwoBall

theorem center_sq2169 : (center2169.re : ℝ)^2 +
    (center2169.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2169]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2169 : work2169.theta.ok = true ∧
    work2169.jac.invOK = true ∧ acceptsUnitSq work2169.out = true := by decide +kernel

def cell2169 : CellCertificate where
  tauBall := tau2169
  contactCenter := center2169
  contactBall := contact2169
  work := work2169
  center_sq := center_sq2169
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2169.1
  jac_ok := checks2169.2.1
  accepted := checks2169.2.2

def tau2170 : RatBall :=
  ⟨⟨-17/320, 23/64⟩, 3/640⟩
def center2170 : GaussianRat :=
  ⟨-5305473/125000000, 65064861/250000000⟩
def contact2170 : RatBall := localContactBall tau2170 center2170
def work2170 : RoundedTauEval :=
  evalTau precision tau2170 contact2170 logTwoBall

theorem center_sq2170 : (center2170.re : ℝ)^2 +
    (center2170.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2170]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2170 : work2170.theta.ok = true ∧
    work2170.jac.invOK = true ∧ acceptsUnitSq work2170.out = true := by decide +kernel

def cell2170 : CellCertificate where
  tauBall := tau2170
  contactCenter := center2170
  contactBall := contact2170
  work := work2170
  center_sq := center_sq2170
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2170.1
  jac_ok := checks2170.2.1
  accepted := checks2170.2.2

def tau2171 : RatBall :=
  ⟨⟨-23/320, 117/320⟩, 3/640⟩
def center2171 : GaussianRat :=
  ⟨-57646751/1000000000, 52885917/200000000⟩
def contact2171 : RatBall := localContactBall tau2171 center2171
def work2171 : RoundedTauEval :=
  evalTau precision tau2171 contact2171 logTwoBall

theorem center_sq2171 : (center2171.re : ℝ)^2 +
    (center2171.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2171]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2171 : work2171.theta.ok = true ∧
    work2171.jac.invOK = true ∧ acceptsUnitSq work2171.out = true := by decide +kernel

def cell2171 : CellCertificate where
  tauBall := tau2171
  contactCenter := center2171
  contactBall := contact2171
  work := work2171
  center_sq := center_sq2171
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2171.1
  jac_ok := checks2171.2.1
  accepted := checks2171.2.2

def tau2172 : RatBall :=
  ⟨⟨-21/320, 117/320⟩, 3/640⟩
def center2172 : GaussianRat :=
  ⟨-52663303/1000000000, 52945801/200000000⟩
def contact2172 : RatBall := localContactBall tau2172 center2172
def work2172 : RoundedTauEval :=
  evalTau precision tau2172 contact2172 logTwoBall

theorem center_sq2172 : (center2172.re : ℝ)^2 +
    (center2172.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2172]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2172 : work2172.theta.ok = true ∧
    work2172.jac.invOK = true ∧ acceptsUnitSq work2172.out = true := by decide +kernel

def cell2172 : CellCertificate where
  tauBall := tau2172
  contactCenter := center2172
  contactBall := contact2172
  work := work2172
  center_sq := center_sq2172
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2172.1
  jac_ok := checks2172.2.1
  accepted := checks2172.2.2

def tau2173 : RatBall :=
  ⟨⟨-23/320, 119/320⟩, 3/640⟩
def center2173 : GaussianRat :=
  ⟨-14490933/250000000, 269422101/1000000000⟩
def contact2173 : RatBall := localContactBall tau2173 center2173
def work2173 : RoundedTauEval :=
  evalTau precision tau2173 contact2173 logTwoBall

theorem center_sq2173 : (center2173.re : ℝ)^2 +
    (center2173.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2173]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2173 : work2173.theta.ok = true ∧
    work2173.jac.invOK = true ∧ acceptsUnitSq work2173.out = true := by decide +kernel

def cell2173 : CellCertificate where
  tauBall := tau2173
  contactCenter := center2173
  contactBall := contact2173
  work := work2173
  center_sq := center_sq2173
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2173.1
  jac_ok := checks2173.2.1
  accepted := checks2173.2.2

def tau2174 : RatBall :=
  ⟨⟨-21/320, 119/320⟩, 3/640⟩
def center2174 : GaussianRat :=
  ⟨-26476749/500000000, 33716241/125000000⟩
def contact2174 : RatBall := localContactBall tau2174 center2174
def work2174 : RoundedTauEval :=
  evalTau precision tau2174 contact2174 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0271


