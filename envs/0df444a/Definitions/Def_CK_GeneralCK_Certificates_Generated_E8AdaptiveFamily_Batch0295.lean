-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0295
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0295
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:24:54.846075+00:00
-- url     : https://prove2.me/theorems/86ff67e2-7da0-497f-8aa2-b03b018063ab
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0295.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0295_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell2365 : CellCertificate where
  tauBall := tau2365
  contactCenter := center2365
  contactBall := contact2365
  work := work2365
  center_sq := center_sq2365
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2365.1
  jac_ok := checks2365.2.1
  accepted := checks2365.2.2

def tau2366 : RatBall :=
  ⟨⟨61/320, 103/320⟩, 3/640⟩
def center2366 : GaussianRat :=
  ⟨5804463/40000000, 221637027/1000000000⟩
def contact2366 : RatBall := localContactBall tau2366 center2366
def work2366 : RoundedTauEval :=
  evalTau precision tau2366 contact2366 logTwoBall

theorem center_sq2366 : (center2366.re : ℝ)^2 +
    (center2366.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2366]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2366 : work2366.theta.ok = true ∧
    work2366.jac.invOK = true ∧ acceptsUnitSq work2366.out = true := by decide +kernel

def cell2366 : CellCertificate where
  tauBall := tau2366
  contactCenter := center2366
  contactBall := contact2366
  work := work2366
  center_sq := center_sq2366
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2366.1
  jac_ok := checks2366.2.1
  accepted := checks2366.2.2

def tau2367 : RatBall :=
  ⟨⟨63/320, 103/320⟩, 3/640⟩
def center2367 : GaussianRat :=
  ⟨74838049/500000000, 221002847/1000000000⟩
def contact2367 : RatBall := localContactBall tau2367 center2367
def work2367 : RoundedTauEval :=
  evalTau precision tau2367 contact2367 logTwoBall

theorem center_sq2367 : (center2367.re : ℝ)^2 +
    (center2367.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2367]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2367 : work2367.theta.ok = true ∧
    work2367.jac.invOK = true ∧ acceptsUnitSq work2367.out = true := by decide +kernel

def cell2367 : CellCertificate where
  tauBall := tau2367
  contactCenter := center2367
  contactBall := contact2367
  work := work2367
  center_sq := center_sq2367
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2367.1
  jac_ok := checks2367.2.1
  accepted := checks2367.2.2

def cells : List CellCertificate := [cell2360, cell2361, cell2362, cell2363, cell2364, cell2365, cell2366, cell2367]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295


