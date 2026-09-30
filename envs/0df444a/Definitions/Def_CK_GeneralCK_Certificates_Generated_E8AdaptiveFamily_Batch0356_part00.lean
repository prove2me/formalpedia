-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0356_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0356_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:39:45.044721+00:00
-- url     : https://prove2.me/theorems/585693d4-5f17-46a2-afd4-71c94d35eda5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0356 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2848 : RatBall :=
  ⟨⟨-23/640, -247/640⟩, 3/1280⟩
def center2848 : GaussianRat :=
  ⟨-1839637/62500000, -141119723/500000000⟩
def contact2848 : RatBall := localContactBall tau2848 center2848
def work2848 : RoundedTauEval :=
  evalTau precision tau2848 contact2848 logTwoBall

theorem center_sq2848 : (center2848.re : ℝ)^2 +
    (center2848.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2848]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2848 : work2848.theta.ok = true ∧
    work2848.jac.invOK = true ∧ acceptsUnitSq work2848.out = true := by decide +kernel

def cell2848 : CellCertificate where
  tauBall := tau2848
  contactCenter := center2848
  contactBall := contact2848
  work := work2848
  center_sq := center_sq2848
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2848.1
  jac_ok := checks2848.2.1
  accepted := checks2848.2.2

def tau2849 : RatBall :=
  ⟨⟨-21/640, -247/640⟩, 3/1280⟩
def center2849 : GaussianRat :=
  ⟨-26878737/1000000000, -282322297/1000000000⟩
def contact2849 : RatBall := localContactBall tau2849 center2849
def work2849 : RoundedTauEval :=
  evalTau precision tau2849 contact2849 logTwoBall

theorem center_sq2849 : (center2849.re : ℝ)^2 +
    (center2849.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2849]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2849 : work2849.theta.ok = true ∧
    work2849.jac.invOK = true ∧ acceptsUnitSq work2849.out = true := by decide +kernel

def cell2849 : CellCertificate where
  tauBall := tau2849
  contactCenter := center2849
  contactBall := contact2849
  work := work2849
  center_sq := center_sq2849
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2849.1
  jac_ok := checks2849.2.1
  accepted := checks2849.2.2

def tau2850 : RatBall :=
  ⟨⟨-23/640, -49/128⟩, 3/1280⟩
def center2850 : GaussianRat :=
  ⟨-7337051/250000000, -279688291/1000000000⟩
def contact2850 : RatBall := localContactBall tau2850 center2850
def work2850 : RoundedTauEval :=
  evalTau precision tau2850 contact2850 logTwoBall

theorem center_sq2850 : (center2850.re : ℝ)^2 +
    (center2850.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2850]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2850 : work2850.theta.ok = true ∧
    work2850.jac.invOK = true ∧ acceptsUnitSq work2850.out = true := by decide +kernel

def cell2850 : CellCertificate where
  tauBall := tau2850
  contactCenter := center2850
  contactBall := contact2850
  work := work2850
  center_sq := center_sq2850
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2850.1
  jac_ok := checks2850.2.1
  accepted := checks2850.2.2

def tau2851 : RatBall :=
  ⟨⟨-21/640, -49/128⟩, 3/1280⟩
def center2851 : GaussianRat :=
  ⟨-6700043/250000000, -139884999/500000000⟩
def contact2851 : RatBall := localContactBall tau2851 center2851
def work2851 : RoundedTauEval :=
  evalTau precision tau2851 contact2851 logTwoBall

theorem center_sq2851 : (center2851.re : ℝ)^2 +
    (center2851.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2851]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2851 : work2851.theta.ok = true ∧
    work2851.jac.invOK = true ∧ acceptsUnitSq work2851.out = true := by decide +kernel

def cell2851 : CellCertificate where
  tauBall := tau2851
  contactCenter := center2851
  contactBall := contact2851
  work := work2851
  center_sq := center_sq2851
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2851.1
  jac_ok := checks2851.2.1
  accepted := checks2851.2.2

def tau2852 : RatBall :=
  ⟨⟨-3/128, -51/128⟩, 3/1280⟩
def center2852 : GaussianRat :=
  ⟨-60747/3125000, -58564523/200000000⟩
def contact2852 : RatBall := localContactBall tau2852 center2852
def work2852 : RoundedTauEval :=
  evalTau precision tau2852 contact2852 logTwoBall

theorem center_sq2852 : (center2852.re : ℝ)^2 +
    (center2852.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2852]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2852 : work2852.theta.ok = true ∧
    work2852.jac.invOK = true ∧ acceptsUnitSq work2852.out = true := by decide +kernel

def cell2852 : CellCertificate where
  tauBall := tau2852
  contactCenter := center2852
  contactBall := contact2852
  work := work2852
  center_sq := center_sq2852
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2852.1
  jac_ok := checks2852.2.1
  accepted := checks2852.2.2

def tau2853 : RatBall :=
  ⟨⟨-13/640, -51/128⟩, 3/1280⟩
def center2853 : GaussianRat :=
  ⟨-3369771/200000000, -146439243/500000000⟩
def contact2853 : RatBall := localContactBall tau2853 center2853

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356


