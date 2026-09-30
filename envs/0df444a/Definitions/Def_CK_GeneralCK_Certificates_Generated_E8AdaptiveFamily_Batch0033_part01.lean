-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0033_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0033_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:26:50.673277+00:00
-- url     : https://prove2.me/theorems/b2bebb3f-216b-49e8-affc-8613f314a8fc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0033 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0033_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact0267 : RatBall := localContactBall tau0267 center0267
def work0267 : RoundedTauEval :=
  evalTau precision tau0267 contact0267 logTwoBall

theorem center_sq0267 : (center0267.re : ℝ)^2 +
    (center0267.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0267]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0267 : work0267.theta.ok = true ∧
    work0267.jac.invOK = true ∧ acceptsUnitSq work0267.out = true := by decide +kernel

def cell0267 : CellCertificate where
  tauBall := tau0267
  contactCenter := center0267
  contactBall := contact0267
  work := work0267
  center_sq := center_sq0267
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0267.1
  jac_ok := checks0267.2.1
  accepted := checks0267.2.2

def tau0268 : RatBall :=
  ⟨⟨-1/80, 21/80⟩, 3/160⟩
def center0268 : GaussianRat :=
  ⟨-4665703/500000000, 93227751/500000000⟩
def contact0268 : RatBall := localContactBall tau0268 center0268
def work0268 : RoundedTauEval :=
  evalTau precision tau0268 contact0268 logTwoBall

theorem center_sq0268 : (center0268.re : ℝ)^2 +
    (center0268.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0268]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0268 : work0268.theta.ok = true ∧
    work0268.jac.invOK = true ∧ acceptsUnitSq work0268.out = true := by decide +kernel

def cell0268 : CellCertificate where
  tauBall := tau0268
  contactCenter := center0268
  contactBall := contact0268
  work := work0268
  center_sq := center_sq0268
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0268.1
  jac_ok := checks0268.2.1
  accepted := checks0268.2.2

def tau0269 : RatBall :=
  ⟨⟨-3/80, 23/80⟩, 3/160⟩
def center0269 : GaussianRat :=
  ⟨-14206169/500000000, 204949543/1000000000⟩
def contact0269 : RatBall := localContactBall tau0269 center0269
def work0269 : RoundedTauEval :=
  evalTau precision tau0269 contact0269 logTwoBall

theorem center_sq0269 : (center0269.re : ℝ)^2 +
    (center0269.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0269]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0269 : work0269.theta.ok = true ∧
    work0269.jac.invOK = true ∧ acceptsUnitSq work0269.out = true := by decide +kernel

def cell0269 : CellCertificate where
  tauBall := tau0269
  contactCenter := center0269
  contactBall := contact0269
  work := work0269
  center_sq := center_sq0269
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0269.1
  jac_ok := checks0269.2.1
  accepted := checks0269.2.2

def tau0270 : RatBall :=
  ⟨⟨-1/80, 23/80⟩, 3/160⟩
def center0270 : GaussianRat :=
  ⟨-4738451/500000000, 102628961/500000000⟩
def contact0270 : RatBall := localContactBall tau0270 center0270
def work0270 : RoundedTauEval :=
  evalTau precision tau0270 contact0270 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033


