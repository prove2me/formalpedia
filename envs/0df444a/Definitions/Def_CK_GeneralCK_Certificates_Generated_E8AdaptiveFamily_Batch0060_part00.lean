-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0060_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0060_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:11:20.827781+00:00
-- url     : https://prove2.me/theorems/5743532f-ef0b-431b-9f33-fdf92df95663
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0060 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0480 : RatBall :=
  ⟨⟨-9/160, -9/32⟩, 3/320⟩
def center0480 : GaussianRat :=
  ⟨-21205027/500000000, -199811247/1000000000⟩
def contact0480 : RatBall := localContactBall tau0480 center0480
def work0480 : RoundedTauEval :=
  evalTau precision tau0480 contact0480 logTwoBall

theorem center_sq0480 : (center0480.re : ℝ)^2 +
    (center0480.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0480]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0480 : work0480.theta.ok = true ∧
    work0480.jac.invOK = true ∧ acceptsUnitSq work0480.out = true := by decide +kernel

def cell0480 : CellCertificate where
  tauBall := tau0480
  contactCenter := center0480
  contactBall := contact0480
  work := work0480
  center_sq := center_sq0480
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0480.1
  jac_ok := checks0480.2.1
  accepted := checks0480.2.2

def tau0481 : RatBall :=
  ⟨⟨-57/160, -29/160⟩, 3/320⟩
def center0481 : GaussianRat :=
  ⟨-243609941/1000000000, -22312087/200000000⟩
def contact0481 : RatBall := localContactBall tau0481 center0481
def work0481 : RoundedTauEval :=
  evalTau precision tau0481 contact0481 logTwoBall

theorem center_sq0481 : (center0481.re : ℝ)^2 +
    (center0481.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0481]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0481 : work0481.theta.ok = true ∧
    work0481.jac.invOK = true ∧ acceptsUnitSq work0481.out = true := by decide +kernel

def cell0481 : CellCertificate where
  tauBall := tau0481
  contactCenter := center0481
  contactBall := contact0481
  work := work0481
  center_sq := center_sq0481
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0481.1
  jac_ok := checks0481.2.1
  accepted := checks0481.2.2

def tau0482 : RatBall :=
  ⟨⟨-59/160, -27/160⟩, 3/320⟩
def center0482 : GaussianRat :=
  ⟨-6260393/25000000, -51450627/500000000⟩
def contact0482 : RatBall := localContactBall tau0482 center0482
def work0482 : RoundedTauEval :=
  evalTau precision tau0482 contact0482 logTwoBall

theorem center_sq0482 : (center0482.re : ℝ)^2 +
    (center0482.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0482]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060


