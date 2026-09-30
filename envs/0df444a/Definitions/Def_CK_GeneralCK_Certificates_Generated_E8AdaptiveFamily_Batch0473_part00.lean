-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0473_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0473_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:21:17.363928+00:00
-- url     : https://prove2.me/theorems/17466d4a-456c-4667-9dac-3269ed78f749
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0473 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3784 : RatBall :=
  ⟨⟨99/640, 231/640⟩, 3/1280⟩
def center3784 : GaussianRat :=
  ⟨122126333/1000000000, 127243109/500000000⟩
def contact3784 : RatBall := localContactBall tau3784 center3784
def work3784 : RoundedTauEval :=
  evalTau precision tau3784 contact3784 logTwoBall

theorem center_sq3784 : (center3784.re : ℝ)^2 +
    (center3784.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3784]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3784 : work3784.theta.ok = true ∧
    work3784.jac.invOK = true ∧ acceptsUnitSq work3784.out = true := by decide +kernel

def cell3784 : CellCertificate where
  tauBall := tau3784
  contactCenter := center3784
  contactBall := contact3784
  work := work3784
  center_sq := center_sq3784
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3784.1
  jac_ok := checks3784.2.1
  accepted := checks3784.2.2

def tau3785 : RatBall :=
  ⟨⟨101/640, 229/640⟩, 3/1280⟩
def center3785 : GaussianRat :=
  ⟨62102193/500000000, 7868253/31250000⟩
def contact3785 : RatBall := localContactBall tau3785 center3785
def work3785 : RoundedTauEval :=
  evalTau precision tau3785 contact3785 logTwoBall

theorem center_sq3785 : (center3785.re : ℝ)^2 +
    (center3785.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3785]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3785 : work3785.theta.ok = true ∧
    work3785.jac.invOK = true ∧ acceptsUnitSq work3785.out = true := by decide +kernel

def cell3785 : CellCertificate where
  tauBall := tau3785
  contactCenter := center3785
  contactBall := contact3785
  work := work3785
  center_sq := center_sq3785
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3785.1
  jac_ok := checks3785.2.1
  accepted := checks3785.2.2

def tau3786 : RatBall :=
  ⟨⟨103/640, 229/640⟩, 3/1280⟩
def center3786 : GaussianRat :=
  ⟨126587587/1000000000, 125734431/500000000⟩
def contact3786 : RatBall := localContactBall tau3786 center3786
def work3786 : RoundedTauEval :=
  evalTau precision tau3786 contact3786 logTwoBall

theorem center_sq3786 : (center3786.re : ℝ)^2 +
    (center3786.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3786]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3786 : work3786.theta.ok = true ∧
    work3786.jac.invOK = true ∧ acceptsUnitSq work3786.out = true := by decide +kernel

def cell3786 : CellCertificate where
  tauBall := tau3786
  contactCenter := center3786
  contactBall := contact3786
  work := work3786
  center_sq := center_sq3786
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3786.1
  jac_ok := checks3786.2.1
  accepted := checks3786.2.2

def tau3787 : RatBall :=
  ⟨⟨101/640, 231/640⟩, 3/1280⟩
def center3787 : GaussianRat :=
  ⟨15564887/125000000, 254172071/1000000000⟩
def contact3787 : RatBall := localContactBall tau3787 center3787
def work3787 : RoundedTauEval :=
  evalTau precision tau3787 contact3787 logTwoBall

theorem center_sq3787 : (center3787.re : ℝ)^2 +
    (center3787.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3787]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3787 : work3787.theta.ok = true ∧
    work3787.jac.invOK = true ∧ acceptsUnitSq work3787.out = true := by decide +kernel

def cell3787 : CellCertificate where
  tauBall := tau3787
  contactCenter := center3787
  contactBall := contact3787
  work := work3787
  center_sq := center_sq3787
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3787.1
  jac_ok := checks3787.2.1
  accepted := checks3787.2.2

def tau3788 : RatBall :=
  ⟨⟨103/640, 231/640⟩, 3/1280⟩
def center3788 : GaussianRat :=
  ⟨63453799/500000000, 253852567/1000000000⟩
def contact3788 : RatBall := localContactBall tau3788 center3788
def work3788 : RoundedTauEval :=
  evalTau precision tau3788 contact3788 logTwoBall

theorem center_sq3788 : (center3788.re : ℝ)^2 +
    (center3788.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3788]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3788 : work3788.theta.ok = true ∧
    work3788.jac.invOK = true ∧ acceptsUnitSq work3788.out = true := by decide +kernel

def cell3788 : CellCertificate where
  tauBall := tau3788
  contactCenter := center3788
  contactBall := contact3788
  work := work3788
  center_sq := center_sq3788
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3788.1
  jac_ok := checks3788.2.1
  accepted := checks3788.2.2

def tau3789 : RatBall :=
  ⟨⟨109/640, 45/128⟩, 3/1280⟩
def center3789 : GaussianRat :=
  ⟨26610681/200000000, 245766093/1000000000⟩
def contact3789 : RatBall := localContactBall tau3789 center3789
def work3789 : RoundedTauEval :=
  evalTau precision tau3789 contact3789 logTwoBall

theorem center_sq3789 : (center3789.re : ℝ)^2 +
    (center3789.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3789]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3789 : work3789.theta.ok = true ∧
    work3789.jac.invOK = true ∧ acceptsUnitSq work3789.out = true := by decide +kernel

def cell3789 : CellCertificate where
  tauBall := tau3789
  contactCenter := center3789
  contactBall := contact3789
  work := work3789
  center_sq := center_sq3789
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3789.1
  jac_ok := checks3789.2.1
  accepted := checks3789.2.2

def tau3790 : RatBall :=
  ⟨⟨111/640, 45/128⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473


