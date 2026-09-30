-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0119_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0119_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:11:38.848645+00:00
-- url     : https://prove2.me/theorems/ddbdd5fb-080b-4993-b457-21e0648aa725
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0119 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0952 : RatBall :=
  ⟨⟨-17/160, 49/160⟩, 3/320⟩
def center0952 : GaussianRat :=
  ⟨-5068403/62500000, 846097/3906250⟩
def contact0952 : RatBall := localContactBall tau0952 center0952
def work0952 : RoundedTauEval :=
  evalTau precision tau0952 contact0952 logTwoBall

theorem center_sq0952 : (center0952.re : ℝ)^2 +
    (center0952.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0952]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0952 : work0952.theta.ok = true ∧
    work0952.jac.invOK = true ∧ acceptsUnitSq work0952.out = true := by decide +kernel

def cell0952 : CellCertificate where
  tauBall := tau0952
  contactCenter := center0952
  contactBall := contact0952
  work := work0952
  center_sq := center_sq0952
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0952.1
  jac_ok := checks0952.2.1
  accepted := checks0952.2.2

def tau0953 : RatBall :=
  ⟨⟨-19/160, 51/160⟩, 3/320⟩
def center0953 : GaussianRat :=
  ⟨-18258621/200000000, 56322187/250000000⟩
def contact0953 : RatBall := localContactBall tau0953 center0953
def work0953 : RoundedTauEval :=
  evalTau precision tau0953 contact0953 logTwoBall

theorem center_sq0953 : (center0953.re : ℝ)^2 +
    (center0953.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0953]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0953 : work0953.theta.ok = true ∧
    work0953.jac.invOK = true ∧ acceptsUnitSq work0953.out = true := by decide +kernel

def cell0953 : CellCertificate where
  tauBall := tau0953
  contactCenter := center0953
  contactBall := contact0953
  work := work0953
  center_sq := center_sq0953
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0953.1
  jac_ok := checks0953.2.1
  accepted := checks0953.2.2

def tau0954 : RatBall :=
  ⟨⟨-17/160, 51/160⟩, 3/320⟩
def center0954 : GaussianRat :=
  ⟨-40905123/500000000, 113032697/500000000⟩
def contact0954 : RatBall := localContactBall tau0954 center0954
def work0954 : RoundedTauEval :=
  evalTau precision tau0954 contact0954 logTwoBall

theorem center_sq0954 : (center0954.re : ℝ)^2 +
    (center0954.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0954]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0954 : work0954.theta.ok = true ∧
    work0954.jac.invOK = true ∧ acceptsUnitSq work0954.out = true := by decide +kernel

def cell0954 : CellCertificate where
  tauBall := tau0954
  contactCenter := center0954
  contactBall := contact0954
  work := work0954
  center_sq := center_sq0954
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0954.1
  jac_ok := checks0954.2.1
  accepted := checks0954.2.2

def tau0955 : RatBall :=
  ⟨⟨-17/160, 53/160⟩, 3/320⟩
def center0955 : GaussianRat :=
  ⟨-82567747/1000000000, 117805603/500000000⟩
def contact0955 : RatBall := localContactBall tau0955 center0955
def work0955 : RoundedTauEval :=
  evalTau precision tau0955 contact0955 logTwoBall

theorem center_sq0955 : (center0955.re : ℝ)^2 +
    (center0955.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0955]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0955 : work0955.theta.ok = true ∧
    work0955.jac.invOK = true ∧ acceptsUnitSq work0955.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119


