-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0024_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0024_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:14:29.021918+00:00
-- url     : https://prove2.me/theorems/a293a7e6-3dd5-47b3-900d-0cc177828eae
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0024 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0024_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact0195 : RatBall := localContactBall tau0195 center0195
def work0195 : RoundedTauEval :=
  evalTau precision tau0195 contact0195 logTwoBall

theorem center_sq0195 : (center0195.re : ℝ)^2 +
    (center0195.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0195]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0195 : work0195.theta.ok = true ∧
    work0195.jac.invOK = true ∧ acceptsUnitSq work0195.out = true := by decide +kernel

def cell0195 : CellCertificate where
  tauBall := tau0195
  contactCenter := center0195
  contactBall := contact0195
  work := work0195
  center_sq := center_sq0195
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0195.1
  jac_ok := checks0195.2.1
  accepted := checks0195.2.2

def tau0196 : RatBall :=
  ⟨⟨29/80, -1/80⟩, 3/160⟩
def center0196 : GaussianRat :=
  ⟨240695961/1000000000, -1905207/250000000⟩
def contact0196 : RatBall := localContactBall tau0196 center0196
def work0196 : RoundedTauEval :=
  evalTau precision tau0196 contact0196 logTwoBall

theorem center_sq0196 : (center0196.re : ℝ)^2 +
    (center0196.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0196]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0196 : work0196.theta.ok = true ∧
    work0196.jac.invOK = true ∧ acceptsUnitSq work0196.out = true := by decide +kernel

def cell0196 : CellCertificate where
  tauBall := tau0196
  contactCenter := center0196
  contactBall := contact0196
  work := work0196
  center_sq := center_sq0196
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0196.1
  jac_ok := checks0196.2.1
  accepted := checks0196.2.2

def tau0197 : RatBall :=
  ⟨⟨31/80, -1/80⟩, 3/160⟩
def center0197 : GaussianRat :=
  ⟨255809887/1000000000, -749167/100000000⟩
def contact0197 : RatBall := localContactBall tau0197 center0197
def work0197 : RoundedTauEval :=
  evalTau precision tau0197 contact0197 logTwoBall

theorem center_sq0197 : (center0197.re : ℝ)^2 +
    (center0197.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0197]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0197 : work0197.theta.ok = true ∧
    work0197.jac.invOK = true ∧ acceptsUnitSq work0197.out = true := by decide +kernel

def cell0197 : CellCertificate where
  tauBall := tau0197
  contactCenter := center0197
  contactBall := contact0197
  work := work0197
  center_sq := center_sq0197
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0197.1
  jac_ok := checks0197.2.1
  accepted := checks0197.2.2

def tau0198 : RatBall :=
  ⟨⟨-31/80, 1/80⟩, 3/160⟩
def center0198 : GaussianRat :=
  ⟨-255809887/1000000000, 749167/100000000⟩
def contact0198 : RatBall := localContactBall tau0198 center0198
def work0198 : RoundedTauEval :=
  evalTau precision tau0198 contact0198 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024


