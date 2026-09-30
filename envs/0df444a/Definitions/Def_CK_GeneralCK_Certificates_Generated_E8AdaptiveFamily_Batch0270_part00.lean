-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0270_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0270_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:53:10.10913+00:00
-- url     : https://prove2.me/theorems/55991dc4-a697-4d04-8278-c2f7146a2e62
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0270 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2160 : RatBall :=
  ⟨⟨-5/64, 117/320⟩, 3/640⟩
def center2160 : GaussianRat :=
  ⟨-3131077/50000000, 66025963/250000000⟩
def contact2160 : RatBall := localContactBall tau2160 center2160
def work2160 : RoundedTauEval :=
  evalTau precision tau2160 contact2160 logTwoBall

theorem center_sq2160 : (center2160.re : ℝ)^2 +
    (center2160.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2160]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2160 : work2160.theta.ok = true ∧
    work2160.jac.invOK = true ∧ acceptsUnitSq work2160.out = true := by decide +kernel

def cell2160 : CellCertificate where
  tauBall := tau2160
  contactCenter := center2160
  contactBall := contact2160
  work := work2160
  center_sq := center_sq2160
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2160.1
  jac_ok := checks2160.2.1
  accepted := checks2160.2.2

def tau2161 : RatBall :=
  ⟨⟨-27/320, 119/320⟩, 3/640⟩
def center2161 : GaussianRat :=
  ⟨-33978407/500000000, 67181393/250000000⟩
def contact2161 : RatBall := localContactBall tau2161 center2161
def work2161 : RoundedTauEval :=
  evalTau precision tau2161 contact2161 logTwoBall

theorem center_sq2161 : (center2161.re : ℝ)^2 +
    (center2161.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2161]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2161 : work2161.theta.ok = true ∧
    work2161.jac.invOK = true ∧ acceptsUnitSq work2161.out = true := by decide +kernel

def cell2161 : CellCertificate where
  tauBall := tau2161
  contactCenter := center2161
  contactBall := contact2161
  work := work2161
  center_sq := center_sq2161
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2161.1
  jac_ok := checks2161.2.1
  accepted := checks2161.2.2

def tau2162 : RatBall :=
  ⟨⟨-5/64, 119/320⟩, 3/640⟩
def center2162 : GaussianRat :=
  ⟨-1574127/25000000, 53817447/200000000⟩
def contact2162 : RatBall := localContactBall tau2162 center2162
def work2162 : RoundedTauEval :=
  evalTau precision tau2162 contact2162 logTwoBall

theorem center_sq2162 : (center2162.re : ℝ)^2 +
    (center2162.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2162]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2162 : work2162.theta.ok = true ∧
    work2162.jac.invOK = true ∧ acceptsUnitSq work2162.out = true := by decide +kernel

def cell2162 : CellCertificate where
  tauBall := tau2162
  contactCenter := center2162
  contactBall := contact2162
  work := work2162
  center_sq := center_sq2162
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2162.1
  jac_ok := checks2162.2.1
  accepted := checks2162.2.2

def tau2163 : RatBall :=
  ⟨⟨-23/320, 113/320⟩, 3/640⟩
def center2163 : GaussianRat :=
  ⟨-57038551/1000000000, 63630699/250000000⟩
def contact2163 : RatBall := localContactBall tau2163 center2163
def work2163 : RoundedTauEval :=
  evalTau precision tau2163 contact2163 logTwoBall

theorem center_sq2163 : (center2163.re : ℝ)^2 +
    (center2163.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2163]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2163 : work2163.theta.ok = true ∧
    work2163.jac.invOK = true ∧ acceptsUnitSq work2163.out = true := by decide +kernel

def cell2163 : CellCertificate where
  tauBall := tau2163
  contactCenter := center2163
  contactBall := contact2163
  work := work2163
  center_sq := center_sq2163
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2163.1
  jac_ok := checks2163.2.1
  accepted := checks2163.2.2

def tau2164 : RatBall :=
  ⟨⟨-21/320, 113/320⟩, 3/640⟩
def center2164 : GaussianRat :=
  ⟨-13026633/250000000, 254806033/1000000000⟩
def contact2164 : RatBall := localContactBall tau2164 center2164
def work2164 : RoundedTauEval :=
  evalTau precision tau2164 contact2164 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270


