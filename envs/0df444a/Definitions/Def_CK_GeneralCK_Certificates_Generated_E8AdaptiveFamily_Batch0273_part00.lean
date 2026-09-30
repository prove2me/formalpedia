-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0273_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0273_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:20:39.974139+00:00
-- url     : https://prove2.me/theorems/f2d3d2f4-3b02-4a31-8e1e-c2c61b189db2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0273 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2184 : RatBall :=
  ⟨⟨-3/64, 23/64⟩, 3/640⟩
def center2184 : GaussianRat :=
  ⟨-37465331/1000000000, 260472693/1000000000⟩
def contact2184 : RatBall := localContactBall tau2184 center2184
def work2184 : RoundedTauEval :=
  evalTau precision tau2184 contact2184 logTwoBall

theorem center_sq2184 : (center2184.re : ℝ)^2 +
    (center2184.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2184]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2184 : work2184.theta.ok = true ∧
    work2184.jac.invOK = true ∧ acceptsUnitSq work2184.out = true := by decide +kernel

def cell2184 : CellCertificate where
  tauBall := tau2184
  contactCenter := center2184
  contactBall := contact2184
  work := work2184
  center_sq := center_sq2184
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2184.1
  jac_ok := checks2184.2.1
  accepted := checks2184.2.2

def tau2185 : RatBall :=
  ⟨⟨-13/320, 23/64⟩, 3/640⟩
def center2185 : GaussianRat :=
  ⟨-32481297/1000000000, 260659621/1000000000⟩
def contact2185 : RatBall := localContactBall tau2185 center2185
def work2185 : RoundedTauEval :=
  evalTau precision tau2185 contact2185 logTwoBall

theorem center_sq2185 : (center2185.re : ℝ)^2 +
    (center2185.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2185]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2185 : work2185.theta.ok = true ∧
    work2185.jac.invOK = true ∧ acceptsUnitSq work2185.out = true := by decide +kernel

def cell2185 : CellCertificate where
  tauBall := tau2185
  contactCenter := center2185
  contactBall := contact2185
  work := work2185
  center_sq := center_sq2185
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2185.1
  jac_ok := checks2185.2.1
  accepted := checks2185.2.2

def tau2186 : RatBall :=
  ⟨⟨-11/320, 113/320⟩, 3/640⟩
def center2186 : GaussianRat :=
  ⟨-5469449/200000000, 51168439/200000000⟩
def contact2186 : RatBall := localContactBall tau2186 center2186
def work2186 : RoundedTauEval :=
  evalTau precision tau2186 contact2186 logTwoBall

theorem center_sq2186 : (center2186.re : ℝ)^2 +
    (center2186.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2186]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2186 : work2186.theta.ok = true ∧
    work2186.jac.invOK = true ∧ acceptsUnitSq work2186.out = true := by decide +kernel

def cell2186 : CellCertificate where
  tauBall := tau2186
  contactCenter := center2186
  contactBall := contact2186
  work := work2186
  center_sq := center_sq2186
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2186.1
  jac_ok := checks2186.2.1
  accepted := checks2186.2.2

def tau2187 : RatBall :=
  ⟨⟨-9/320, 113/320⟩, 3/640⟩
def center2187 : GaussianRat :=
  ⟨-22380501/1000000000, 127986203/500000000⟩
def contact2187 : RatBall := localContactBall tau2187 center2187
def work2187 : RoundedTauEval :=
  evalTau precision tau2187 contact2187 logTwoBall

theorem center_sq2187 : (center2187.re : ℝ)^2 +
    (center2187.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2187]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2187 : work2187.theta.ok = true ∧
    work2187.jac.invOK = true ∧ acceptsUnitSq work2187.out = true := by decide +kernel

def cell2187 : CellCertificate where
  tauBall := tau2187
  contactCenter := center2187
  contactBall := contact2187
  work := work2187
  center_sq := center_sq2187
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2187.1
  jac_ok := checks2187.2.1
  accepted := checks2187.2.2

def tau2188 : RatBall :=
  ⟨⟨-11/320, 23/64⟩, 3/640⟩
def center2188 : GaussianRat :=
  ⟨-27492413/1000000000, 2037657/7812500⟩
def contact2188 : RatBall := localContactBall tau2188 center2188
def work2188 : RoundedTauEval :=
  evalTau precision tau2188 contact2188 logTwoBall

theorem center_sq2188 : (center2188.re : ℝ)^2 +
    (center2188.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2188]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2188 : work2188.theta.ok = true ∧
    work2188.jac.invOK = true ∧ acceptsUnitSq work2188.out = true := by decide +kernel

def cell2188 : CellCertificate where
  tauBall := tau2188
  contactCenter := center2188
  contactBall := contact2188
  work := work2188
  center_sq := center_sq2188
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2188.1
  jac_ok := checks2188.2.1
  accepted := checks2188.2.2

def tau2189 : RatBall :=
  ⟨⟨-9/320, 23/64⟩, 3/640⟩
def center2189 : GaussianRat :=
  ⟨-22499417/1000000000, 260954001/1000000000⟩
def contact2189 : RatBall := localContactBall tau2189 center2189
def work2189 : RoundedTauEval :=
  evalTau precision tau2189 contact2189 logTwoBall

theorem center_sq2189 : (center2189.re : ℝ)^2 +
    (center2189.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2189]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2189 : work2189.theta.ok = true ∧
    work2189.jac.invOK = true ∧ acceptsUnitSq work2189.out = true := by decide +kernel

def cell2189 : CellCertificate where
  tauBall := tau2189
  contactCenter := center2189
  contactBall := contact2189
  work := work2189
  center_sq := center_sq2189
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2189.1
  jac_ok := checks2189.2.1
  accepted := checks2189.2.2

def tau2190 : RatBall :=
  ⟨⟨-3/64, 117/320⟩, 3/640⟩
def center2190 : GaussianRat :=
  ⟨-18834129/500000000, 13273367/50000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273


