-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0352_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0352_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:10:08.381147+00:00
-- url     : https://prove2.me/theorems/6909f17f-a402-49ef-8d24-111718a926b5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0352 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2816 : RatBall :=
  ⟨⟨-31/640, -251/640⟩, 3/1280⟩
def center2816 : GaussianRat :=
  ⟨-4984851/125000000, -286946953/1000000000⟩
def contact2816 : RatBall := localContactBall tau2816 center2816
def work2816 : RoundedTauEval :=
  evalTau precision tau2816 contact2816 logTwoBall

theorem center_sq2816 : (center2816.re : ℝ)^2 +
    (center2816.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2816]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2816 : work2816.theta.ok = true ∧
    work2816.jac.invOK = true ∧ acceptsUnitSq work2816.out = true := by decide +kernel

def cell2816 : CellCertificate where
  tauBall := tau2816
  contactCenter := center2816
  contactBall := contact2816
  work := work2816
  center_sq := center_sq2816
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2816.1
  jac_ok := checks2816.2.1
  accepted := checks2816.2.2

def tau2817 : RatBall :=
  ⟨⟨-29/640, -251/640⟩, 3/1280⟩
def center2817 : GaussianRat :=
  ⟨-1865689/50000000, -287062723/1000000000⟩
def contact2817 : RatBall := localContactBall tau2817 center2817
def work2817 : RoundedTauEval :=
  evalTau precision tau2817 contact2817 logTwoBall

theorem center_sq2817 : (center2817.re : ℝ)^2 +
    (center2817.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2817]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2817 : work2817.theta.ok = true ∧
    work2817.jac.invOK = true ∧ acceptsUnitSq work2817.out = true := by decide +kernel

def cell2817 : CellCertificate where
  tauBall := tau2817
  contactCenter := center2817
  contactBall := contact2817
  work := work2817
  center_sq := center_sq2817
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2817.1
  jac_ok := checks2817.2.1
  accepted := checks2817.2.2

def tau2818 : RatBall :=
  ⟨⟨-31/640, -249/640⟩, 3/1280⟩
def center2818 : GaussianRat :=
  ⟨-19880031/500000000, -56877303/200000000⟩
def contact2818 : RatBall := localContactBall tau2818 center2818
def work2818 : RoundedTauEval :=
  evalTau precision tau2818 contact2818 logTwoBall

theorem center_sq2818 : (center2818.re : ℝ)^2 +
    (center2818.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2818]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2818 : work2818.theta.ok = true ∧
    work2818.jac.invOK = true ∧ acceptsUnitSq work2818.out = true := by decide +kernel

def cell2818 : CellCertificate where
  tauBall := tau2818
  contactCenter := center2818
  contactBall := contact2818
  work := work2818
  center_sq := center_sq2818
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2818.1
  jac_ok := checks2818.2.1
  accepted := checks2818.2.2

def tau2819 : RatBall :=
  ⟨⟨-29/640, -249/640⟩, 3/1280⟩
def center2819 : GaussianRat :=
  ⟨-37202587/1000000000, -284500691/1000000000⟩
def contact2819 : RatBall := localContactBall tau2819 center2819
def work2819 : RoundedTauEval :=
  evalTau precision tau2819 contact2819 logTwoBall

theorem center_sq2819 : (center2819.re : ℝ)^2 +
    (center2819.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2819]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2819 : work2819.theta.ok = true ∧
    work2819.jac.invOK = true ∧ acceptsUnitSq work2819.out = true := by decide +kernel

def cell2819 : CellCertificate where
  tauBall := tau2819
  contactCenter := center2819
  contactBall := contact2819
  work := work2819
  center_sq := center_sq2819
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2819.1
  jac_ok := checks2819.2.1
  accepted := checks2819.2.2

def tau2820 : RatBall :=
  ⟨⟨-27/640, -251/640⟩, 3/1280⟩
def center2820 : GaussianRat :=
  ⟨-17373599/500000000, -287170877/1000000000⟩
def contact2820 : RatBall := localContactBall tau2820 center2820
def work2820 : RoundedTauEval :=
  evalTau precision tau2820 contact2820 logTwoBall

theorem center_sq2820 : (center2820.re : ℝ)^2 +
    (center2820.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2820]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2820 : work2820.theta.ok = true ∧
    work2820.jac.invOK = true ∧ acceptsUnitSq work2820.out = true := by decide +kernel

def cell2820 : CellCertificate where
  tauBall := tau2820
  contactCenter := center2820
  contactBall := contact2820
  work := work2820
  center_sq := center_sq2820
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2820.1
  jac_ok := checks2820.2.1
  accepted := checks2820.2.2

def tau2821 : RatBall :=
  ⟨⟨-5/128, -251/640⟩, 3/1280⟩
def center2821 : GaussianRat :=
  ⟨-32179167/1000000000, -57454279/200000000⟩
def contact2821 : RatBall := localContactBall tau2821 center2821
def work2821 : RoundedTauEval :=
  evalTau precision tau2821 contact2821 logTwoBall

theorem center_sq2821 : (center2821.re : ℝ)^2 +
    (center2821.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2821]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352


