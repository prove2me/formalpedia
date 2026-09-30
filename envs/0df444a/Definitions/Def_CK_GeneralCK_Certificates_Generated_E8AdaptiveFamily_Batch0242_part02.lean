-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0242_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0242_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:18:36.468416+00:00
-- url     : https://prove2.me/theorems/febda2ea-e472-47e8-933a-ddf116f66cc9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 3 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 3 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 3 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 3 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0242 (part 3 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0242_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1940 : RatBall :=
  ⟨⟨-91/320, 91/320⟩, 3/640⟩
def center1940 : GaussianRat :=
  ⟨-51739029/250000000, 46278317/250000000⟩
def contact1940 : RatBall := localContactBall tau1940 center1940
def work1940 : RoundedTauEval :=
  evalTau precision tau1940 contact1940 logTwoBall

theorem center_sq1940 : (center1940.re : ℝ)^2 +
    (center1940.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1940]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1940 : work1940.theta.ok = true ∧
    work1940.jac.invOK = true ∧ acceptsUnitSq work1940.out = true := by decide +kernel

def cell1940 : CellCertificate where
  tauBall := tau1940
  contactCenter := center1940
  contactBall := contact1940
  work := work1940
  center_sq := center_sq1940
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1940.1
  jac_ok := checks1940.2.1
  accepted := checks1940.2.2

def tau1941 : RatBall :=
  ⟨⟨-89/320, 91/320⟩, 3/640⟩
def center1941 : GaussianRat :=
  ⟨-202731249/1000000000, 37163483/200000000⟩
def contact1941 : RatBall := localContactBall tau1941 center1941
def work1941 : RoundedTauEval :=
  evalTau precision tau1941 contact1941 logTwoBall

theorem center_sq1941 : (center1941.re : ℝ)^2 +
    (center1941.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1941]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1941 : work1941.theta.ok = true ∧
    work1941.jac.invOK = true ∧ acceptsUnitSq work1941.out = true := by decide +kernel

def cell1941 : CellCertificate where
  tauBall := tau1941
  contactCenter := center1941
  contactBall := contact1941
  work := work1941
  center_sq := center_sq1941
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1941.1
  jac_ok := checks1941.2.1
  accepted := checks1941.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242


