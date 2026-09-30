-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0275_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0275_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:11:06.838204+00:00
-- url     : https://prove2.me/theorems/93346ef1-80d1-4704-85b3-cfec4ccfff8e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0275 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2200 : RatBall :=
  ⟨⟨-7/320, 23/64⟩, 3/640⟩
def center2200 : GaussianRat :=
  ⟨-350061/20000000, 130530621/500000000⟩
def contact2200 : RatBall := localContactBall tau2200 center2200
def work2200 : RoundedTauEval :=
  evalTau precision tau2200 contact2200 logTwoBall

theorem center_sq2200 : (center2200.re : ℝ)^2 +
    (center2200.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2200]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2200 : work2200.theta.ok = true ∧
    work2200.jac.invOK = true ∧ acceptsUnitSq work2200.out = true := by decide +kernel

def cell2200 : CellCertificate where
  tauBall := tau2200
  contactCenter := center2200
  contactBall := contact2200
  work := work2200
  center_sq := center_sq2200
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2200.1
  jac_ok := checks2200.2.1
  accepted := checks2200.2.2

def tau2201 : RatBall :=
  ⟨⟨-1/64, 23/64⟩, 3/640⟩
def center2201 : GaussianRat :=
  ⟨-1563007/125000000, 13057087/50000000⟩
def contact2201 : RatBall := localContactBall tau2201 center2201
def work2201 : RoundedTauEval :=
  evalTau precision tau2201 contact2201 logTwoBall

theorem center_sq2201 : (center2201.re : ℝ)^2 +
    (center2201.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2201]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2201 : work2201.theta.ok = true ∧
    work2201.jac.invOK = true ∧ acceptsUnitSq work2201.out = true := by decide +kernel

def cell2201 : CellCertificate where
  tauBall := tau2201
  contactCenter := center2201
  contactBall := contact2201
  work := work2201
  center_sq := center_sq2201
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2201.1
  jac_ok := checks2201.2.1
  accepted := checks2201.2.2

def tau2202 : RatBall :=
  ⟨⟨-7/320, 117/320⟩, 3/640⟩
def center2202 : GaussianRat :=
  ⟨-3519651/200000000, 8314767/31250000⟩
def contact2202 : RatBall := localContactBall tau2202 center2202
def work2202 : RoundedTauEval :=
  evalTau precision tau2202 contact2202 logTwoBall

theorem center_sq2202 : (center2202.re : ℝ)^2 +
    (center2202.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2202]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2202 : work2202.theta.ok = true ∧
    work2202.jac.invOK = true ∧ acceptsUnitSq work2202.out = true := by decide +kernel

def cell2202 : CellCertificate where
  tauBall := tau2202
  contactCenter := center2202
  contactBall := contact2202
  work := work2202
  center_sq := center_sq2202
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2202.1
  jac_ok := checks2202.2.1
  accepted := checks2202.2.2

def tau2203 : RatBall :=
  ⟨⟨-1/64, 117/320⟩, 3/640⟩
def center2203 : GaussianRat :=
  ⟨-1257211/100000000, 66538831/250000000⟩
def contact2203 : RatBall := localContactBall tau2203 center2203
def work2203 : RoundedTauEval :=
  evalTau precision tau2203 contact2203 logTwoBall

theorem center_sq2203 : (center2203.re : ℝ)^2 +
    (center2203.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2203]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2203 : work2203.theta.ok = true ∧
    work2203.jac.invOK = true ∧ acceptsUnitSq work2203.out = true := by decide +kernel

def cell2203 : CellCertificate where
  tauBall := tau2203
  contactCenter := center2203
  contactBall := contact2203
  work := work2203
  center_sq := center_sq2203
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2203.1
  jac_ok := checks2203.2.1
  accepted := checks2203.2.2

def tau2204 : RatBall :=
  ⟨⟨-7/320, 119/320⟩, 3/640⟩
def center2204 : GaussianRat :=
  ⟨-3539231/200000000, 67777837/250000000⟩
def contact2204 : RatBall := localContactBall tau2204 center2204
def work2204 : RoundedTauEval :=
  evalTau precision tau2204 contact2204 logTwoBall

theorem center_sq2204 : (center2204.re : ℝ)^2 +
    (center2204.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2204]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2204 : work2204.theta.ok = true ∧
    work2204.jac.invOK = true ∧ acceptsUnitSq work2204.out = true := by decide +kernel

def cell2204 : CellCertificate where
  tauBall := tau2204
  contactCenter := center2204
  contactBall := contact2204
  work := work2204
  center_sq := center_sq2204
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2204.1
  jac_ok := checks2204.2.1
  accepted := checks2204.2.2

def tau2205 : RatBall :=
  ⟨⟨-1/64, 119/320⟩, 3/640⟩
def center2205 : GaussianRat :=
  ⟨-1264209/100000000, 27119647/100000000⟩
def contact2205 : RatBall := localContactBall tau2205 center2205
def work2205 : RoundedTauEval :=
  evalTau precision tau2205 contact2205 logTwoBall

theorem center_sq2205 : (center2205.re : ℝ)^2 +
    (center2205.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2205]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2205 : work2205.theta.ok = true ∧
    work2205.jac.invOK = true ∧ acceptsUnitSq work2205.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275


