-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0272_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0272_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:01:53.115489+00:00
-- url     : https://prove2.me/theorems/cc0d32a0-9897-4345-904b-2beac8e8d0cf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0272 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2176 : RatBall :=
  ⟨⟨-17/320, 117/320⟩, 3/640⟩
def center2176 : GaussianRat :=
  ⟨-10668331/250000000, 265248069/1000000000⟩
def contact2176 : RatBall := localContactBall tau2176 center2176
def work2176 : RoundedTauEval :=
  evalTau precision tau2176 contact2176 logTwoBall

theorem center_sq2176 : (center2176.re : ℝ)^2 +
    (center2176.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2176]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2176 : work2176.theta.ok = true ∧
    work2176.jac.invOK = true ∧ acceptsUnitSq work2176.out = true := by decide +kernel

def cell2176 : CellCertificate where
  tauBall := tau2176
  contactCenter := center2176
  contactBall := contact2176
  work := work2176
  center_sq := center_sq2176
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2176.1
  jac_ok := checks2176.2.1
  accepted := checks2176.2.2

def tau2177 : RatBall :=
  ⟨⟨-19/320, 119/320⟩, 3/640⟩
def center2177 : GaussianRat :=
  ⟨-47935117/1000000000, 2109457/7812500⟩
def contact2177 : RatBall := localContactBall tau2177 center2177
def work2177 : RoundedTauEval :=
  evalTau precision tau2177 contact2177 logTwoBall

theorem center_sq2177 : (center2177.re : ℝ)^2 +
    (center2177.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2177]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2177 : work2177.theta.ok = true ∧
    work2177.jac.invOK = true ∧ acceptsUnitSq work2177.out = true := by decide +kernel

def cell2177 : CellCertificate where
  tauBall := tau2177
  contactCenter := center2177
  contactBall := contact2177
  work := work2177
  center_sq := center_sq2177
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2177.1
  jac_ok := checks2177.2.1
  accepted := checks2177.2.2

def tau2178 : RatBall :=
  ⟨⟨-17/320, 119/320⟩, 3/640⟩
def center2178 : GaussianRat :=
  ⟨-42909337/1000000000, 135131799/500000000⟩
def contact2178 : RatBall := localContactBall tau2178 center2178
def work2178 : RoundedTauEval :=
  evalTau precision tau2178 contact2178 logTwoBall

theorem center_sq2178 : (center2178.re : ℝ)^2 +
    (center2178.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2178]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2178 : work2178.theta.ok = true ∧
    work2178.jac.invOK = true ∧ acceptsUnitSq work2178.out = true := by decide +kernel

def cell2178 : CellCertificate where
  tauBall := tau2178
  contactCenter := center2178
  contactBall := contact2178
  work := work2178
  center_sq := center_sq2178
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2178.1
  jac_ok := checks2178.2.1
  accepted := checks2178.2.2

def tau2179 : RatBall :=
  ⟨⟨-21/320, 121/320⟩, 3/640⟩
def center2179 : GaussianRat :=
  ⟨-53251841/1000000000, 54951623/200000000⟩
def contact2179 : RatBall := localContactBall tau2179 center2179
def work2179 : RoundedTauEval :=
  evalTau precision tau2179 contact2179 logTwoBall

theorem center_sq2179 : (center2179.re : ℝ)^2 +
    (center2179.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2179]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2179 : work2179.theta.ok = true ∧
    work2179.jac.invOK = true ∧ acceptsUnitSq work2179.out = true := by decide +kernel

def cell2179 : CellCertificate where
  tauBall := tau2179
  contactCenter := center2179
  contactBall := contact2179
  work := work2179
  center_sq := center_sq2179
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2179.1
  jac_ok := checks2179.2.1
  accepted := checks2179.2.2

def tau2180 : RatBall :=
  ⟨⟨-19/320, 121/320⟩, 3/640⟩
def center2180 : GaussianRat :=
  ⟨-48205717/1000000000, 275046561/1000000000⟩
def contact2180 : RatBall := localContactBall tau2180 center2180
def work2180 : RoundedTauEval :=
  evalTau precision tau2180 contact2180 logTwoBall

theorem center_sq2180 : (center2180.re : ℝ)^2 +
    (center2180.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2180]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2180 : work2180.theta.ok = true ∧
    work2180.jac.invOK = true ∧ acceptsUnitSq work2180.out = true := by decide +kernel

def cell2180 : CellCertificate where
  tauBall := tau2180
  contactCenter := center2180
  contactBall := contact2180
  work := work2180
  center_sq := center_sq2180
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2180.1
  jac_ok := checks2180.2.1
  accepted := checks2180.2.2

def tau2181 : RatBall :=
  ⟨⟨-17/320, 121/320⟩, 3/640⟩
def center2181 : GaussianRat :=
  ⟨-8630399/200000000, 275306779/1000000000⟩
def contact2181 : RatBall := localContactBall tau2181 center2181
def work2181 : RoundedTauEval :=
  evalTau precision tau2181 contact2181 logTwoBall

theorem center_sq2181 : (center2181.re : ℝ)^2 +
    (center2181.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2181]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2181 : work2181.theta.ok = true ∧
    work2181.jac.invOK = true ∧ acceptsUnitSq work2181.out = true := by decide +kernel

def cell2181 : CellCertificate where
  tauBall := tau2181
  contactCenter := center2181
  contactBall := contact2181
  work := work2181
  center_sq := center_sq2181
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2181.1
  jac_ok := checks2181.2.1
  accepted := checks2181.2.2

def tau2182 : RatBall :=
  ⟨⟨-3/64, 113/320⟩, 3/640⟩
def center2182 : GaussianRat :=
  ⟨-18633993/500000000, 15969023/62500000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272


