-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0297
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0297
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:52:25.084711+00:00
-- url     : https://prove2.me/theorems/c1a71837-09b6-4614-8481-ab545c340810
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0297.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0297_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2381 : work2381.theta.ok = true ∧
    work2381.jac.invOK = true ∧ acceptsUnitSq work2381.out = true := by decide +kernel

def cell2381 : CellCertificate where
  tauBall := tau2381
  contactCenter := center2381
  contactBall := contact2381
  work := work2381
  center_sq := center_sq2381
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2381.1
  jac_ok := checks2381.2.1
  accepted := checks2381.2.2

def tau2382 : RatBall :=
  ⟨⟨53/320, 111/320⟩, 3/640⟩
def center2382 : GaussianRat :=
  ⟨4032529/31250000, 121353177/500000000⟩
def contact2382 : RatBall := localContactBall tau2382 center2382
def work2382 : RoundedTauEval :=
  evalTau precision tau2382 contact2382 logTwoBall

theorem center_sq2382 : (center2382.re : ℝ)^2 +
    (center2382.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2382]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2382 : work2382.theta.ok = true ∧
    work2382.jac.invOK = true ∧ acceptsUnitSq work2382.out = true := by decide +kernel

def cell2382 : CellCertificate where
  tauBall := tau2382
  contactCenter := center2382
  contactBall := contact2382
  work := work2382
  center_sq := center_sq2382
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2382.1
  jac_ok := checks2382.2.1
  accepted := checks2382.2.2

def tau2383 : RatBall :=
  ⟨⟨11/64, 111/320⟩, 3/640⟩
def center2383 : GaussianRat :=
  ⟨133746201/1000000000, 121037589/500000000⟩
def contact2383 : RatBall := localContactBall tau2383 center2383
def work2383 : RoundedTauEval :=
  evalTau precision tau2383 contact2383 logTwoBall

theorem center_sq2383 : (center2383.re : ℝ)^2 +
    (center2383.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2383]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2383 : work2383.theta.ok = true ∧
    work2383.jac.invOK = true ∧ acceptsUnitSq work2383.out = true := by decide +kernel

def cell2383 : CellCertificate where
  tauBall := tau2383
  contactCenter := center2383
  contactBall := contact2383
  work := work2383
  center_sq := center_sq2383
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2383.1
  jac_ok := checks2383.2.1
  accepted := checks2383.2.2

def cells : List CellCertificate := [cell2376, cell2377, cell2378, cell2379, cell2380, cell2381, cell2382, cell2383]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297


