-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0353_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0353_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:28:49.662131+00:00
-- url     : https://prove2.me/theorems/de34f8bd-d2e6-4c2a-bf59-1aa4ccb4d8c0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0353 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2824 : RatBall :=
  ⟨⟨-23/640, -51/128⟩, 3/1280⟩
def center2824 : GaussianRat :=
  ⟨-5958069/200000000, -292519767/1000000000⟩
def contact2824 : RatBall := localContactBall tau2824 center2824
def work2824 : RoundedTauEval :=
  evalTau precision tau2824 contact2824 logTwoBall

theorem center_sq2824 : (center2824.re : ℝ)^2 +
    (center2824.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2824]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2824 : work2824.theta.ok = true ∧
    work2824.jac.invOK = true ∧ acceptsUnitSq work2824.out = true := by decide +kernel

def cell2824 : CellCertificate where
  tauBall := tau2824
  contactCenter := center2824
  contactBall := contact2824
  work := work2824
  center_sq := center_sq2824
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2824.1
  jac_ok := checks2824.2.1
  accepted := checks2824.2.2

def tau2825 : RatBall :=
  ⟨⟨-21/640, -51/128⟩, 3/1280⟩
def center2825 : GaussianRat :=
  ⟨-27204153/1000000000, -58521471/200000000⟩
def contact2825 : RatBall := localContactBall tau2825 center2825
def work2825 : RoundedTauEval :=
  evalTau precision tau2825 contact2825 logTwoBall

theorem center_sq2825 : (center2825.re : ℝ)^2 +
    (center2825.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2825]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2825 : work2825.theta.ok = true ∧
    work2825.jac.invOK = true ∧ acceptsUnitSq work2825.out = true := by decide +kernel

def cell2825 : CellCertificate where
  tauBall := tau2825
  contactCenter := center2825
  contactBall := contact2825
  work := work2825
  center_sq := center_sq2825
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2825.1
  jac_ok := checks2825.2.1
  accepted := checks2825.2.2

def tau2826 : RatBall :=
  ⟨⟨-23/640, -253/640⟩, 3/1280⟩
def center2826 : GaussianRat :=
  ⟨-14849721/500000000, -7248453/25000000⟩
def contact2826 : RatBall := localContactBall tau2826 center2826
def work2826 : RoundedTauEval :=
  evalTau precision tau2826 contact2826 logTwoBall

theorem center_sq2826 : (center2826.re : ℝ)^2 +
    (center2826.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2826]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2826 : work2826.theta.ok = true ∧
    work2826.jac.invOK = true ∧ acceptsUnitSq work2826.out = true := by decide +kernel

def cell2826 : CellCertificate where
  tauBall := tau2826
  contactCenter := center2826
  contactBall := contact2826
  work := work2826
  center_sq := center_sq2826
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2826.1
  jac_ok := checks2826.2.1
  accepted := checks2826.2.2

def tau2827 : RatBall :=
  ⟨⟨-21/640, -253/640⟩, 3/1280⟩
def center2827 : GaussianRat :=
  ⟨-5424219/200000000, -290024499/1000000000⟩
def contact2827 : RatBall := localContactBall tau2827 center2827
def work2827 : RoundedTauEval :=
  evalTau precision tau2827 contact2827 logTwoBall

theorem center_sq2827 : (center2827.re : ℝ)^2 +
    (center2827.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2827]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2827 : work2827.theta.ok = true ∧
    work2827.jac.invOK = true ∧ acceptsUnitSq work2827.out = true := by decide +kernel

def cell2827 : CellCertificate where
  tauBall := tau2827
  contactCenter := center2827
  contactBall := contact2827
  work := work2827
  center_sq := center_sq2827
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2827.1
  jac_ok := checks2827.2.1
  accepted := checks2827.2.2

def tau2828 : RatBall :=
  ⟨⟨-19/640, -51/128⟩, 3/1280⟩
def center2828 : GaussianRat :=
  ⟨-24616799/1000000000, -73171759/250000000⟩
def contact2828 : RatBall := localContactBall tau2828 center2828
def work2828 : RoundedTauEval :=
  evalTau precision tau2828 contact2828 logTwoBall

theorem center_sq2828 : (center2828.re : ℝ)^2 +
    (center2828.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2828]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2828 : work2828.theta.ok = true ∧
    work2828.jac.invOK = true ∧ acceptsUnitSq work2828.out = true := by decide +kernel

def cell2828 : CellCertificate where
  tauBall := tau2828
  contactCenter := center2828
  contactBall := contact2828
  work := work2828
  center_sq := center_sq2828
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2828.1
  jac_ok := checks2828.2.1
  accepted := checks2828.2.2

def tau2829 : RatBall :=
  ⟨⟨-17/640, -51/128⟩, 3/1280⟩
def center2829 : GaussianRat :=
  ⟨-22028391/1000000000, -146379397/500000000⟩
def contact2829 : RatBall := localContactBall tau2829 center2829
def work2829 : RoundedTauEval :=
  evalTau precision tau2829 contact2829 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353


