-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0355_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0355_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:31:05.729969+00:00
-- url     : https://prove2.me/theorems/5d60a9be-9030-40b1-be00-889f84f76736
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0355 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2840 : RatBall :=
  ⟨⟨-31/640, -247/640⟩, 3/1280⟩
def center2840 : GaussianRat :=
  ⟨-4955369/125000000, -8807299/31250000⟩
def contact2840 : RatBall := localContactBall tau2840 center2840
def work2840 : RoundedTauEval :=
  evalTau precision tau2840 contact2840 logTwoBall

theorem center_sq2840 : (center2840.re : ℝ)^2 +
    (center2840.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2840]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2840 : work2840.theta.ok = true ∧
    work2840.jac.invOK = true ∧ acceptsUnitSq work2840.out = true := by decide +kernel

def cell2840 : CellCertificate where
  tauBall := tau2840
  contactCenter := center2840
  contactBall := contact2840
  work := work2840
  center_sq := center_sq2840
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2840.1
  jac_ok := checks2840.2.1
  accepted := checks2840.2.2

def tau2841 : RatBall :=
  ⟨⟨-29/640, -247/640⟩, 3/1280⟩
def center2841 : GaussianRat :=
  ⟨-18546463/500000000, -281946171/1000000000⟩
def contact2841 : RatBall := localContactBall tau2841 center2841
def work2841 : RoundedTauEval :=
  evalTau precision tau2841 contact2841 logTwoBall

theorem center_sq2841 : (center2841.re : ℝ)^2 +
    (center2841.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2841]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2841 : work2841.theta.ok = true ∧
    work2841.jac.invOK = true ∧ acceptsUnitSq work2841.out = true := by decide +kernel

def cell2841 : CellCertificate where
  tauBall := tau2841
  contactCenter := center2841
  contactBall := contact2841
  work := work2841
  center_sq := center_sq2841
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2841.1
  jac_ok := checks2841.2.1
  accepted := checks2841.2.2

def tau2842 : RatBall :=
  ⟨⟨-31/640, -49/128⟩, 3/1280⟩
def center2842 : GaussianRat :=
  ⟨-19763727/500000000, -279288009/1000000000⟩
def contact2842 : RatBall := localContactBall tau2842 center2842
def work2842 : RoundedTauEval :=
  evalTau precision tau2842 contact2842 logTwoBall

theorem center_sq2842 : (center2842.re : ℝ)^2 +
    (center2842.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2842]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2842 : work2842.theta.ok = true ∧
    work2842.jac.invOK = true ∧ acceptsUnitSq work2842.out = true := by decide +kernel

def cell2842 : CellCertificate where
  tauBall := tau2842
  contactCenter := center2842
  contactBall := contact2842
  work := work2842
  center_sq := center_sq2842
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2842.1
  jac_ok := checks2842.2.1
  accepted := checks2842.2.2

def tau2843 : RatBall :=
  ⟨⟨-29/640, -49/128⟩, 3/1280⟩
def center2843 : GaussianRat :=
  ⟨-4623097/125000000, -13969953/50000000⟩
def contact2843 : RatBall := localContactBall tau2843 center2843
def work2843 : RoundedTauEval :=
  evalTau precision tau2843 contact2843 logTwoBall

theorem center_sq2843 : (center2843.re : ℝ)^2 +
    (center2843.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2843]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2843 : work2843.theta.ok = true ∧
    work2843.jac.invOK = true ∧ acceptsUnitSq work2843.out = true := by decide +kernel

def cell2843 : CellCertificate where
  tauBall := tau2843
  contactCenter := center2843
  contactBall := contact2843
  work := work2843
  center_sq := center_sq2843
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2843.1
  jac_ok := checks2843.2.1
  accepted := checks2843.2.2

def tau2844 : RatBall :=
  ⟨⟨-27/640, -247/640⟩, 3/1280⟩
def center2844 : GaussianRat :=
  ⟨-34541389/1000000000, -56410273/200000000⟩
def contact2844 : RatBall := localContactBall tau2844 center2844
def work2844 : RoundedTauEval :=
  evalTau precision tau2844 contact2844 logTwoBall

theorem center_sq2844 : (center2844.re : ℝ)^2 +
    (center2844.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2844]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2844 : work2844.theta.ok = true ∧
    work2844.jac.invOK = true ∧ acceptsUnitSq work2844.out = true := by decide +kernel

def cell2844 : CellCertificate where
  tauBall := tau2844
  contactCenter := center2844
  contactBall := contact2844
  work := work2844
  center_sq := center_sq2844
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2844.1
  jac_ok := checks2844.2.1
  accepted := checks2844.2.2

def tau2845 : RatBall :=
  ⟨⟨-5/128, -247/640⟩, 3/1280⟩
def center2845 : GaussianRat :=
  ⟨-7997111/250000000, -282149129/1000000000⟩
def contact2845 : RatBall := localContactBall tau2845 center2845
def work2845 : RoundedTauEval :=
  evalTau precision tau2845 contact2845 logTwoBall

theorem center_sq2845 : (center2845.re : ℝ)^2 +
    (center2845.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2845]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355


