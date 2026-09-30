-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0273
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0273
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:35:49.480904+00:00
-- url     : https://prove2.me/theorems/ded8fe38-867f-4298-87cb-52c02f2d3e40
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0273.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0273_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact2190 : RatBall := localContactBall tau2190 center2190
def work2190 : RoundedTauEval :=
  evalTau precision tau2190 contact2190 logTwoBall

theorem center_sq2190 : (center2190.re : ℝ)^2 +
    (center2190.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2190]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2190 : work2190.theta.ok = true ∧
    work2190.jac.invOK = true ∧ acceptsUnitSq work2190.out = true := by decide +kernel

def cell2190 : CellCertificate where
  tauBall := tau2190
  contactCenter := center2190
  contactBall := contact2190
  work := work2190
  center_sq := center_sq2190
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2190.1
  jac_ok := checks2190.2.1
  accepted := checks2190.2.2

def tau2191 : RatBall :=
  ⟨⟨-13/320, 117/320⟩, 3/640⟩
def center2191 : GaussianRat :=
  ⟨-6531493/200000000, 265659553/1000000000⟩
def contact2191 : RatBall := localContactBall tau2191 center2191
def work2191 : RoundedTauEval :=
  evalTau precision tau2191 contact2191 logTwoBall

theorem center_sq2191 : (center2191.re : ℝ)^2 +
    (center2191.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2191]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2191 : work2191.theta.ok = true ∧
    work2191.jac.invOK = true ∧ acceptsUnitSq work2191.out = true := by decide +kernel

def cell2191 : CellCertificate where
  tauBall := tau2191
  contactCenter := center2191
  contactBall := contact2191
  work := work2191
  center_sq := center_sq2191
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2191.1
  jac_ok := checks2191.2.1
  accepted := checks2191.2.2

def cells : List CellCertificate := [cell2184, cell2185, cell2186, cell2187, cell2188, cell2189, cell2190, cell2191]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273


