-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0047_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0047_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:05:21.16663+00:00
-- url     : https://prove2.me/theorems/6dd74cad-f5c9-43c5-aafc-5c23efaa76af
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0047 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0376 : RatBall :=
  ⟨⟨-41/160, -33/160⟩, 3/320⟩
def center0376 : GaussianRat :=
  ⟨-180884951/1000000000, -135214257/1000000000⟩
def contact0376 : RatBall := localContactBall tau0376 center0376
def work0376 : RoundedTauEval :=
  evalTau precision tau0376 contact0376 logTwoBall

theorem center_sq0376 : (center0376.re : ℝ)^2 +
    (center0376.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0376]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0376 : work0376.theta.ok = true ∧
    work0376.jac.invOK = true ∧ acceptsUnitSq work0376.out = true := by decide +kernel

def cell0376 : CellCertificate where
  tauBall := tau0376
  contactCenter := center0376
  contactBall := contact0376
  work := work0376
  center_sq := center_sq0376
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0376.1
  jac_ok := checks0376.2.1
  accepted := checks0376.2.2

def tau0377 : RatBall :=
  ⟨⟨-39/160, -39/160⟩, 3/320⟩
def center0377 : GaussianRat :=
  ⟨-7014647/40000000, -32307527/200000000⟩
def contact0377 : RatBall := localContactBall tau0377 center0377
def work0377 : RoundedTauEval :=
  evalTau precision tau0377 contact0377 logTwoBall

theorem center_sq0377 : (center0377.re : ℝ)^2 +
    (center0377.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0377]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0377 : work0377.theta.ok = true ∧
    work0377.jac.invOK = true ∧ acceptsUnitSq work0377.out = true := by decide +kernel

def cell0377 : CellCertificate where
  tauBall := tau0377
  contactCenter := center0377
  contactBall := contact0377
  work := work0377
  center_sq := center_sq0377
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0377.1
  jac_ok := checks0377.2.1
  accepted := checks0377.2.2

def tau0378 : RatBall :=
  ⟨⟨-37/160, -39/160⟩, 3/320⟩
def center0378 : GaussianRat :=
  ⟨-83398769/500000000, -20321547/125000000⟩
def contact0378 : RatBall := localContactBall tau0378 center0378
def work0378 : RoundedTauEval :=
  evalTau precision tau0378 contact0378 logTwoBall

theorem center_sq0378 : (center0378.re : ℝ)^2 +
    (center0378.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0378]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0378 : work0378.theta.ok = true ∧
    work0378.jac.invOK = true ∧ acceptsUnitSq work0378.out = true := by decide +kernel

def cell0378 : CellCertificate where
  tauBall := tau0378
  contactCenter := center0378
  contactBall := contact0378
  work := work0378
  center_sq := center_sq0378
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0378.1
  jac_ok := checks0378.2.1
  accepted := checks0378.2.2

def tau0379 : RatBall :=
  ⟨⟨-39/160, -37/160⟩, 3/320⟩
def center0379 : GaussianRat :=
  ⟨-174343743/1000000000, -153020771/1000000000⟩
def contact0379 : RatBall := localContactBall tau0379 center0379
def work0379 : RoundedTauEval :=
  evalTau precision tau0379 contact0379 logTwoBall

theorem center_sq0379 : (center0379.re : ℝ)^2 +
    (center0379.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0379]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0379 : work0379.theta.ok = true ∧
    work0379.jac.invOK = true ∧ acceptsUnitSq work0379.out = true := by decide +kernel

def cell0379 : CellCertificate where
  tauBall := tau0379
  contactCenter := center0379
  contactBall := contact0379
  work := work0379
  center_sq := center_sq0379
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0379.1
  jac_ok := checks0379.2.1
  accepted := checks0379.2.2

def tau0380 : RatBall :=
  ⟨⟨-37/160, -37/160⟩, 3/320⟩
def center0380 : GaussianRat :=
  ⟨-33162899/200000000, -153992113/1000000000⟩
def contact0380 : RatBall := localContactBall tau0380 center0380
def work0380 : RoundedTauEval :=
  evalTau precision tau0380 contact0380 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047


