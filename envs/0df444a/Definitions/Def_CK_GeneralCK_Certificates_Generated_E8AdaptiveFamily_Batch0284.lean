-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0284
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0284
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:23:33.066755+00:00
-- url     : https://prove2.me/theorems/e3829016-ff6d-4ae8-88d0-12145940ec08
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0284` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0284` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0284` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0284 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0284.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0284_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0284

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center2278 : GaussianRat :=
  ⟨47166967/1000000000, 255064157/1000000000⟩
def contact2278 : RatBall := localContactBall tau2278 center2278
def work2278 : RoundedTauEval :=
  evalTau precision tau2278 contact2278 logTwoBall

theorem center_sq2278 : (center2278.re : ℝ)^2 +
    (center2278.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2278]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2278 : work2278.theta.ok = true ∧
    work2278.jac.invOK = true ∧ acceptsUnitSq work2278.out = true := by decide +kernel

def cell2278 : CellCertificate where
  tauBall := tau2278
  contactCenter := center2278
  contactBall := contact2278
  work := work2278
  center_sq := center_sq2278
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2278.1
  jac_ok := checks2278.2.1
  accepted := checks2278.2.2

def tau2279 : RatBall :=
  ⟨⟨17/320, 23/64⟩, 3/640⟩
def center2279 : GaussianRat :=
  ⟨5305473/125000000, 65064861/250000000⟩
def contact2279 : RatBall := localContactBall tau2279 center2279
def work2279 : RoundedTauEval :=
  evalTau precision tau2279 contact2279 logTwoBall

theorem center_sq2279 : (center2279.re : ℝ)^2 +
    (center2279.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2279]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2279 : work2279.theta.ok = true ∧
    work2279.jac.invOK = true ∧ acceptsUnitSq work2279.out = true := by decide +kernel

def cell2279 : CellCertificate where
  tauBall := tau2279
  contactCenter := center2279
  contactBall := contact2279
  work := work2279
  center_sq := center_sq2279
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2279.1
  jac_ok := checks2279.2.1
  accepted := checks2279.2.2

def cells : List CellCertificate := [cell2272, cell2273, cell2274, cell2275, cell2276, cell2277, cell2278, cell2279]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0284


