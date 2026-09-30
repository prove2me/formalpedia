-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0042
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0042
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:35:55.427862+00:00
-- url     : https://prove2.me/theorems/d027151d-fc93-44b8-b11d-36eb66136ba6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0042.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0042_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact0342 : RatBall := localContactBall tau0342 center0342
def work0342 : RoundedTauEval :=
  evalTau precision tau0342 contact0342 logTwoBall

theorem center_sq0342 : (center0342.re : ℝ)^2 +
    (center0342.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0342]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0342 : work0342.theta.ok = true ∧
    work0342.jac.invOK = true ∧ acceptsUnitSq work0342.out = true := by decide +kernel

def cell0342 : CellCertificate where
  tauBall := tau0342
  contactCenter := center0342
  contactBall := contact0342
  work := work0342
  center_sq := center_sq0342
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0342.1
  jac_ok := checks0342.2.1
  accepted := checks0342.2.2

def tau0343 : RatBall :=
  ⟨⟨3/16, 17/80⟩, 3/160⟩
def center0343 : GaussianRat :=
  ⟨16793263/125000000, 143981719/1000000000⟩
def contact0343 : RatBall := localContactBall tau0343 center0343
def work0343 : RoundedTauEval :=
  evalTau precision tau0343 contact0343 logTwoBall

theorem center_sq0343 : (center0343.re : ℝ)^2 +
    (center0343.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0343]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0343 : work0343.theta.ok = true ∧
    work0343.jac.invOK = true ∧ acceptsUnitSq work0343.out = true := by decide +kernel

def cell0343 : CellCertificate where
  tauBall := tau0343
  contactCenter := center0343
  contactBall := contact0343
  work := work0343
  center_sq := center_sq0343
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0343.1
  jac_ok := checks0343.2.1
  accepted := checks0343.2.2

def cells : List CellCertificate := [cell0336, cell0337, cell0338, cell0339, cell0340, cell0341, cell0342, cell0343]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042


