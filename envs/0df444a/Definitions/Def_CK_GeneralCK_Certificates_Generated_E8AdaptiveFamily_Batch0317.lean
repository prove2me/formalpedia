-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0317
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0317
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:53:28.933549+00:00
-- url     : https://prove2.me/theorems/c4e7fc7f-8aa6-41fb-b631-ee3cb4fffcdf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0317` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0317` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0317` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0317 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0317.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0317_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0317

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2542 : RatBall :=
  ⟨⟨77/320, 99/320⟩, 3/640⟩
def center2542 : GaussianRat :=
  ⟨179660917/1000000000, 207308367/1000000000⟩
def contact2542 : RatBall := localContactBall tau2542 center2542
def work2542 : RoundedTauEval :=
  evalTau precision tau2542 contact2542 logTwoBall

theorem center_sq2542 : (center2542.re : ℝ)^2 +
    (center2542.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2542]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2542 : work2542.theta.ok = true ∧
    work2542.jac.invOK = true ∧ acceptsUnitSq work2542.out = true := by decide +kernel

def cell2542 : CellCertificate where
  tauBall := tau2542
  contactCenter := center2542
  contactBall := contact2542
  work := work2542
  center_sq := center_sq2542
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2542.1
  jac_ok := checks2542.2.1
  accepted := checks2542.2.2

def tau2543 : RatBall :=
  ⟨⟨79/320, 99/320⟩, 3/640⟩
def center2543 : GaussianRat :=
  ⟨184048527/1000000000, 206594091/1000000000⟩
def contact2543 : RatBall := localContactBall tau2543 center2543
def work2543 : RoundedTauEval :=
  evalTau precision tau2543 contact2543 logTwoBall

theorem center_sq2543 : (center2543.re : ℝ)^2 +
    (center2543.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2543]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2543 : work2543.theta.ok = true ∧
    work2543.jac.invOK = true ∧ acceptsUnitSq work2543.out = true := by decide +kernel

def cell2543 : CellCertificate where
  tauBall := tau2543
  contactCenter := center2543
  contactBall := contact2543
  work := work2543
  center_sq := center_sq2543
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2543.1
  jac_ok := checks2543.2.1
  accepted := checks2543.2.2

def cells : List CellCertificate := [cell2536, cell2537, cell2538, cell2539, cell2540, cell2541, cell2542, cell2543]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0317


