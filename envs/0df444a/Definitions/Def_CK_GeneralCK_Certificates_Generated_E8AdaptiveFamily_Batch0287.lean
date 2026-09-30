-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0287
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0287
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:50:40.339031+00:00
-- url     : https://prove2.me/theorems/e4fa90bf-6ff5-4e87-a99e-925c878df1f0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0287` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0287` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0287` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0287 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0287.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0287_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0287

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work2302 : RoundedTauEval :=
  evalTau precision tau2302 contact2302 logTwoBall

theorem center_sq2302 : (center2302.re : ℝ)^2 +
    (center2302.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2302]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2302 : work2302.theta.ok = true ∧
    work2302.jac.invOK = true ∧ acceptsUnitSq work2302.out = true := by decide +kernel

def cell2302 : CellCertificate where
  tauBall := tau2302
  contactCenter := center2302
  contactBall := contact2302
  work := work2302
  center_sq := center_sq2302
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2302.1
  jac_ok := checks2302.2.1
  accepted := checks2302.2.2

def tau2303 : RatBall :=
  ⟨⟨5/64, 119/320⟩, 3/640⟩
def center2303 : GaussianRat :=
  ⟨1574127/25000000, 53817447/200000000⟩
def contact2303 : RatBall := localContactBall tau2303 center2303
def work2303 : RoundedTauEval :=
  evalTau precision tau2303 contact2303 logTwoBall

theorem center_sq2303 : (center2303.re : ℝ)^2 +
    (center2303.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2303]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2303 : work2303.theta.ok = true ∧
    work2303.jac.invOK = true ∧ acceptsUnitSq work2303.out = true := by decide +kernel

def cell2303 : CellCertificate where
  tauBall := tau2303
  contactCenter := center2303
  contactBall := contact2303
  work := work2303
  center_sq := center_sq2303
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2303.1
  jac_ok := checks2303.2.1
  accepted := checks2303.2.2

def cells : List CellCertificate := [cell2296, cell2297, cell2298, cell2299, cell2300, cell2301, cell2302, cell2303]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0287


