-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0342_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0342_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:29:26.806804+00:00
-- url     : https://prove2.me/theorems/08534bc1-ac2b-4898-b170-cc098fda64c2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0342 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2736 : RatBall :=
  ⟨⟨-61/640, -49/128⟩, 3/1280⟩
def center2736 : GaussianRat :=
  ⟨-3096871/40000000, -138381321/500000000⟩
def contact2736 : RatBall := localContactBall tau2736 center2736
def work2736 : RoundedTauEval :=
  evalTau precision tau2736 contact2736 logTwoBall

theorem center_sq2736 : (center2736.re : ℝ)^2 +
    (center2736.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2736]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2736 : work2736.theta.ok = true ∧
    work2736.jac.invOK = true ∧ acceptsUnitSq work2736.out = true := by decide +kernel

def cell2736 : CellCertificate where
  tauBall := tau2736
  contactCenter := center2736
  contactBall := contact2736
  work := work2736
  center_sq := center_sq2736
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2736.1
  jac_ok := checks2736.2.1
  accepted := checks2736.2.2

def tau2737 : RatBall :=
  ⟨⟨-59/640, -247/640⟩, 3/1280⟩
def center2737 : GaussianRat :=
  ⟨-75128671/1000000000, -55898717/200000000⟩
def contact2737 : RatBall := localContactBall tau2737 center2737
def work2737 : RoundedTauEval :=
  evalTau precision tau2737 contact2737 logTwoBall

theorem center_sq2737 : (center2737.re : ℝ)^2 +
    (center2737.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2737]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2737 : work2737.theta.ok = true ∧
    work2737.jac.invOK = true ∧ acceptsUnitSq work2737.out = true := by decide +kernel

def cell2737 : CellCertificate where
  tauBall := tau2737
  contactCenter := center2737
  contactBall := contact2737
  work := work2737
  center_sq := center_sq2737
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2737.1
  jac_ok := checks2737.2.1
  accepted := checks2737.2.2

def tau2738 : RatBall :=
  ⟨⟨-57/640, -247/640⟩, 3/1280⟩
def center2738 : GaussianRat :=
  ⟨-72610227/1000000000, -34963383/125000000⟩
def contact2738 : RatBall := localContactBall tau2738 center2738
def work2738 : RoundedTauEval :=
  evalTau precision tau2738 contact2738 logTwoBall

theorem center_sq2738 : (center2738.re : ℝ)^2 +
    (center2738.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2738]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2738 : work2738.theta.ok = true ∧
    work2738.jac.invOK = true ∧ acceptsUnitSq work2738.out = true := by decide +kernel

def cell2738 : CellCertificate where
  tauBall := tau2738
  contactCenter := center2738
  contactBall := contact2738
  work := work2738
  center_sq := center_sq2738
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2738.1
  jac_ok := checks2738.2.1
  accepted := checks2738.2.2

def tau2739 : RatBall :=
  ⟨⟨-59/640, -49/128⟩, 3/1280⟩
def center2739 : GaussianRat :=
  ⟨-7491319/100000000, -34622509/125000000⟩
def contact2739 : RatBall := localContactBall tau2739 center2739
def work2739 : RoundedTauEval :=
  evalTau precision tau2739 contact2739 logTwoBall

theorem center_sq2739 : (center2739.re : ℝ)^2 +
    (center2739.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2739]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2739 : work2739.theta.ok = true ∧
    work2739.jac.invOK = true ∧ acceptsUnitSq work2739.out = true := by decide +kernel

def cell2739 : CellCertificate where
  tauBall := tau2739
  contactCenter := center2739
  contactBall := contact2739
  work := work2739
  center_sq := center_sq2739
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2739.1
  jac_ok := checks2739.2.1
  accepted := checks2739.2.2

def tau2740 : RatBall :=
  ⟨⟨-57/640, -49/128⟩, 3/1280⟩
def center2740 : GaussianRat :=
  ⟨-7240167/100000000, -277190643/1000000000⟩
def contact2740 : RatBall := localContactBall tau2740 center2740
def work2740 : RoundedTauEval :=
  evalTau precision tau2740 contact2740 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342


