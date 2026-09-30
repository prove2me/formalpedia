-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0293
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0293
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:38:41.400903+00:00
-- url     : https://prove2.me/theorems/4d1f1bdf-7b61-4001-94f6-4fcd54c4bf9e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0293.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0293_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2349 : work2349.theta.ok = true ∧
    work2349.jac.invOK = true ∧ acceptsUnitSq work2349.out = true := by decide +kernel

def cell2349 : CellCertificate where
  tauBall := tau2349
  contactCenter := center2349
  contactBall := contact2349
  work := work2349
  center_sq := center_sq2349
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2349.1
  jac_ok := checks2349.2.1
  accepted := checks2349.2.2

def tau2350 : RatBall :=
  ⟨⟨53/320, 103/320⟩, 3/640⟩
def center2350 : GaussianRat :=
  ⟨126686203/1000000000, 224004631/1000000000⟩
def contact2350 : RatBall := localContactBall tau2350 center2350
def work2350 : RoundedTauEval :=
  evalTau precision tau2350 contact2350 logTwoBall

theorem center_sq2350 : (center2350.re : ℝ)^2 +
    (center2350.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2350]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2350 : work2350.theta.ok = true ∧
    work2350.jac.invOK = true ∧ acceptsUnitSq work2350.out = true := by decide +kernel

def cell2350 : CellCertificate where
  tauBall := tau2350
  contactCenter := center2350
  contactBall := contact2350
  work := work2350
  center_sq := center_sq2350
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2350.1
  jac_ok := checks2350.2.1
  accepted := checks2350.2.2

def tau2351 : RatBall :=
  ⟨⟨11/64, 103/320⟩, 3/640⟩
def center2351 : GaussianRat :=
  ⟨8207299/62500000, 8937551/40000000⟩
def contact2351 : RatBall := localContactBall tau2351 center2351
def work2351 : RoundedTauEval :=
  evalTau precision tau2351 contact2351 logTwoBall

theorem center_sq2351 : (center2351.re : ℝ)^2 +
    (center2351.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2351]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2351 : work2351.theta.ok = true ∧
    work2351.jac.invOK = true ∧ acceptsUnitSq work2351.out = true := by decide +kernel

def cell2351 : CellCertificate where
  tauBall := tau2351
  contactCenter := center2351
  contactBall := contact2351
  work := work2351
  center_sq := center_sq2351
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2351.1
  jac_ok := checks2351.2.1
  accepted := checks2351.2.2

def cells : List CellCertificate := [cell2344, cell2345, cell2346, cell2347, cell2348, cell2349, cell2350, cell2351]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293


