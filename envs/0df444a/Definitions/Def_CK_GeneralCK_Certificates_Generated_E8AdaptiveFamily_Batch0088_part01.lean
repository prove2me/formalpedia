-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0088_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0088_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:29:49.396225+00:00
-- url     : https://prove2.me/theorems/a766183b-4150-49e3-956d-c23d0fffec15
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0088 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0088_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact0707 : RatBall := localContactBall tau0707 center0707
def work0707 : RoundedTauEval :=
  evalTau precision tau0707 contact0707 logTwoBall

theorem center_sq0707 : (center0707.re : ℝ)^2 +
    (center0707.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0707]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0707 : work0707.theta.ok = true ∧
    work0707.jac.invOK = true ∧ acceptsUnitSq work0707.out = true := by decide +kernel

def cell0707 : CellCertificate where
  tauBall := tau0707
  contactCenter := center0707
  contactBall := contact0707
  work := work0707
  center_sq := center_sq0707
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0707.1
  jac_ok := checks0707.2.1
  accepted := checks0707.2.2

def tau0708 : RatBall :=
  ⟨⟨47/160, -27/160⟩, 3/320⟩
def center0708 : GaussianRat :=
  ⟨5075841/25000000, -107985769/1000000000⟩
def contact0708 : RatBall := localContactBall tau0708 center0708
def work0708 : RoundedTauEval :=
  evalTau precision tau0708 contact0708 logTwoBall

theorem center_sq0708 : (center0708.re : ℝ)^2 +
    (center0708.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0708]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0708 : work0708.theta.ok = true ∧
    work0708.jac.invOK = true ∧ acceptsUnitSq work0708.out = true := by decide +kernel

def cell0708 : CellCertificate where
  tauBall := tau0708
  contactCenter := center0708
  contactBall := contact0708
  work := work0708
  center_sq := center_sq0708
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0708.1
  jac_ok := checks0708.2.1
  accepted := checks0708.2.2

def tau0709 : RatBall :=
  ⟨⟨9/32, -5/32⟩, 3/320⟩
def center0709 : GaussianRat :=
  ⟨194169161/1000000000, -100614871/1000000000⟩
def contact0709 : RatBall := localContactBall tau0709 center0709
def work0709 : RoundedTauEval :=
  evalTau precision tau0709 contact0709 logTwoBall

theorem center_sq0709 : (center0709.re : ℝ)^2 +
    (center0709.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0709]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0709 : work0709.theta.ok = true ∧
    work0709.jac.invOK = true ∧ acceptsUnitSq work0709.out = true := by decide +kernel

def cell0709 : CellCertificate where
  tauBall := tau0709
  contactCenter := center0709
  contactBall := contact0709
  work := work0709
  center_sq := center_sq0709
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0709.1
  jac_ok := checks0709.2.1
  accepted := checks0709.2.2

def tau0710 : RatBall :=
  ⟨⟨47/160, -5/32⟩, 3/320⟩
def center0710 : GaussianRat :=
  ⟨202276259/1000000000, -49949641/500000000⟩
def contact0710 : RatBall := localContactBall tau0710 center0710
def work0710 : RoundedTauEval :=
  evalTau precision tau0710 contact0710 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088


