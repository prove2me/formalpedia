-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0282
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0282
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:12:32.0176+00:00
-- url     : https://prove2.me/theorems/0bd8b56a-972a-4cdc-9f46-23eb8f08ef8c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0282.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0282_part02

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work2262 : RoundedTauEval :=
  evalTau precision tau2262 contact2262 logTwoBall

theorem center_sq2262 : (center2262.re : ℝ)^2 +
    (center2262.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2262]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2262 : work2262.theta.ok = true ∧
    work2262.jac.invOK = true ∧ acceptsUnitSq work2262.out = true := by decide +kernel

def cell2262 : CellCertificate where
  tauBall := tau2262
  contactCenter := center2262
  contactBall := contact2262
  work := work2262
  center_sq := center_sq2262
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2262.1
  jac_ok := checks2262.2.1
  accepted := checks2262.2.2

def tau2263 : RatBall :=
  ⟨⟨3/64, 119/320⟩, 3/640⟩
def center2263 : GaussianRat :=
  ⟨18938457/500000000, 5409781/20000000⟩
def contact2263 : RatBall := localContactBall tau2263 center2263
def work2263 : RoundedTauEval :=
  evalTau precision tau2263 contact2263 logTwoBall

theorem center_sq2263 : (center2263.re : ℝ)^2 +
    (center2263.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2263]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2263 : work2263.theta.ok = true ∧
    work2263.jac.invOK = true ∧ acceptsUnitSq work2263.out = true := by decide +kernel

def cell2263 : CellCertificate where
  tauBall := tau2263
  contactCenter := center2263
  contactBall := contact2263
  work := work2263
  center_sq := center_sq2263
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2263.1
  jac_ok := checks2263.2.1
  accepted := checks2263.2.2

def cells : List CellCertificate := [cell2256, cell2257, cell2258, cell2259, cell2260, cell2261, cell2262, cell2263]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282


