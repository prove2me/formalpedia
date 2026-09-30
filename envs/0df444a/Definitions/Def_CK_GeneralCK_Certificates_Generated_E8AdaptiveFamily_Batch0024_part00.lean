-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0024_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0024_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:22:21.470662+00:00
-- url     : https://prove2.me/theorems/5b9869a3-ed38-4f0a-b880-b6758356d5f2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0024 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0192 : RatBall :=
  ⟨⟨27/80, -3/80⟩, 3/160⟩
def center0192 : GaussianRat :=
  ⟨225572371/1000000000, -4648277/200000000⟩
def contact0192 : RatBall := localContactBall tau0192 center0192
def work0192 : RoundedTauEval :=
  evalTau precision tau0192 contact0192 logTwoBall

theorem center_sq0192 : (center0192.re : ℝ)^2 +
    (center0192.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0192 : work0192.theta.ok = true ∧
    work0192.jac.invOK = true ∧ acceptsUnitSq work0192.out = true := by decide +kernel

def cell0192 : CellCertificate where
  tauBall := tau0192
  contactCenter := center0192
  contactBall := contact0192
  work := work0192
  center_sq := center_sq0192
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0192.1
  jac_ok := checks0192.2.1
  accepted := checks0192.2.2

def tau0193 : RatBall :=
  ⟨⟨5/16, -1/80⟩, 3/160⟩
def center0193 : GaussianRat :=
  ⟨104858117/500000000, -3932321/500000000⟩
def contact0193 : RatBall := localContactBall tau0193 center0193
def work0193 : RoundedTauEval :=
  evalTau precision tau0193 contact0193 logTwoBall

theorem center_sq0193 : (center0193.re : ℝ)^2 +
    (center0193.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0193]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0193 : work0193.theta.ok = true ∧
    work0193.jac.invOK = true ∧ acceptsUnitSq work0193.out = true := by decide +kernel

def cell0193 : CellCertificate where
  tauBall := tau0193
  contactCenter := center0193
  contactBall := contact0193
  work := work0193
  center_sq := center_sq0193
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0193.1
  jac_ok := checks0193.2.1
  accepted := checks0193.2.2

def tau0194 : RatBall :=
  ⟨⟨27/80, -1/80⟩, 3/160⟩
def center0194 : GaussianRat :=
  ⟨45065623/200000000, -7745371/1000000000⟩
def contact0194 : RatBall := localContactBall tau0194 center0194
def work0194 : RoundedTauEval :=
  evalTau precision tau0194 contact0194 logTwoBall

theorem center_sq0194 : (center0194.re : ℝ)^2 +
    (center0194.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0194]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0194 : work0194.theta.ok = true ∧
    work0194.jac.invOK = true ∧ acceptsUnitSq work0194.out = true := by decide +kernel

def cell0194 : CellCertificate where
  tauBall := tau0194
  contactCenter := center0194
  contactBall := contact0194
  work := work0194
  center_sq := center_sq0194
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0194.1
  jac_ok := checks0194.2.1
  accepted := checks0194.2.2

def tau0195 : RatBall :=
  ⟨⟨29/80, -3/80⟩, 3/160⟩
def center0195 : GaussianRat :=
  ⟨120475049/500000000, -4573419/200000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024


