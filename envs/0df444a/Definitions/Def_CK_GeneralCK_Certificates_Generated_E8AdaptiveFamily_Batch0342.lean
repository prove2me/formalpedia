-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0342
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0342
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:29:26.172192+00:00
-- url     : https://prove2.me/theorems/79a06172-2cd8-459a-9678-0b6d3a284c68
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0342.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0342_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2740 : (center2740.re : ℝ)^2 +
    (center2740.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2740]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2740 : work2740.theta.ok = true ∧
    work2740.jac.invOK = true ∧ acceptsUnitSq work2740.out = true := by decide +kernel

def cell2740 : CellCertificate where
  tauBall := tau2740
  contactCenter := center2740
  contactBall := contact2740
  work := work2740
  center_sq := center_sq2740
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2740.1
  jac_ok := checks2740.2.1
  accepted := checks2740.2.2

def tau2741 : RatBall :=
  ⟨⟨-63/640, -243/640⟩, 3/1280⟩
def center2741 : GaussianRat :=
  ⟨-79701237/1000000000, -274037749/1000000000⟩
def contact2741 : RatBall := localContactBall tau2741 center2741
def work2741 : RoundedTauEval :=
  evalTau precision tau2741 contact2741 logTwoBall

theorem center_sq2741 : (center2741.re : ℝ)^2 +
    (center2741.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2741]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2741 : work2741.theta.ok = true ∧
    work2741.jac.invOK = true ∧ acceptsUnitSq work2741.out = true := by decide +kernel

def cell2741 : CellCertificate where
  tauBall := tau2741
  contactCenter := center2741
  contactBall := contact2741
  work := work2741
  center_sq := center_sq2741
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2741.1
  jac_ok := checks2741.2.1
  accepted := checks2741.2.2

def tau2742 : RatBall :=
  ⟨⟨-61/640, -243/640⟩, 3/1280⟩
def center2742 : GaussianRat :=
  ⟨-77202433/1000000000, -5485179/20000000⟩
def contact2742 : RatBall := localContactBall tau2742 center2742
def work2742 : RoundedTauEval :=
  evalTau precision tau2742 contact2742 logTwoBall

theorem center_sq2742 : (center2742.re : ℝ)^2 +
    (center2742.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2742]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2742 : work2742.theta.ok = true ∧
    work2742.jac.invOK = true ∧ acceptsUnitSq work2742.out = true := by decide +kernel

def cell2742 : CellCertificate where
  tauBall := tau2742
  contactCenter := center2742
  contactBall := contact2742
  work := work2742
  center_sq := center_sq2742
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2742.1
  jac_ok := checks2742.2.1
  accepted := checks2742.2.2

def tau2743 : RatBall :=
  ⟨⟨-63/640, -241/640⟩, 3/1280⟩
def center2743 : GaussianRat :=
  ⟨-15895643/200000000, -271543799/1000000000⟩
def contact2743 : RatBall := localContactBall tau2743 center2743
def work2743 : RoundedTauEval :=
  evalTau precision tau2743 contact2743 logTwoBall

theorem center_sq2743 : (center2743.re : ℝ)^2 +
    (center2743.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2743]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2743 : work2743.theta.ok = true ∧
    work2743.jac.invOK = true ∧ acceptsUnitSq work2743.out = true := by decide +kernel

def cell2743 : CellCertificate where
  tauBall := tau2743
  contactCenter := center2743
  contactBall := contact2743
  work := work2743
  center_sq := center_sq2743
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2743.1
  jac_ok := checks2743.2.1
  accepted := checks2743.2.2

def cells : List CellCertificate := [cell2736, cell2737, cell2738, cell2739, cell2740, cell2741, cell2742, cell2743]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342


