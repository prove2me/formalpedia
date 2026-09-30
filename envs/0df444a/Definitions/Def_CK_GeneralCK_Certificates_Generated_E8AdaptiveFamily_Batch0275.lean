-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0275
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0275
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:52:37.035495+00:00
-- url     : https://prove2.me/theorems/6f26a672-80c2-420f-8a16-37edc2cfd6ae
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0275.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0275_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell2205 : CellCertificate where
  tauBall := tau2205
  contactCenter := center2205
  contactBall := contact2205
  work := work2205
  center_sq := center_sq2205
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2205.1
  jac_ok := checks2205.2.1
  accepted := checks2205.2.2

def tau2206 : RatBall :=
  ⟨⟨-3/320, 117/320⟩, 3/640⟩
def center2206 : GaussianRat :=
  ⟨-7544037/1000000000, 16638159/62500000⟩
def contact2206 : RatBall := localContactBall tau2206 center2206
def work2206 : RoundedTauEval :=
  evalTau precision tau2206 contact2206 logTwoBall

theorem center_sq2206 : (center2206.re : ℝ)^2 +
    (center2206.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2206]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2206 : work2206.theta.ok = true ∧
    work2206.jac.invOK = true ∧ acceptsUnitSq work2206.out = true := by decide +kernel

def cell2206 : CellCertificate where
  tauBall := tau2206
  contactCenter := center2206
  contactBall := contact2206
  work := work2206
  center_sq := center_sq2206
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2206.1
  jac_ok := checks2206.2.1
  accepted := checks2206.2.2

def tau2207 : RatBall :=
  ⟨⟨-1/320, 117/320⟩, 3/640⟩
def center2207 : GaussianRat :=
  ⟨-314351/125000000, 66559541/250000000⟩
def contact2207 : RatBall := localContactBall tau2207 center2207
def work2207 : RoundedTauEval :=
  evalTau precision tau2207 contact2207 logTwoBall

theorem center_sq2207 : (center2207.re : ℝ)^2 +
    (center2207.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2207]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2207 : work2207.theta.ok = true ∧
    work2207.jac.invOK = true ∧ acceptsUnitSq work2207.out = true := by decide +kernel

def cell2207 : CellCertificate where
  tauBall := tau2207
  contactCenter := center2207
  contactBall := contact2207
  work := work2207
  center_sq := center_sq2207
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2207.1
  jac_ok := checks2207.2.1
  accepted := checks2207.2.2

def cells : List CellCertificate := [cell2200, cell2201, cell2202, cell2203, cell2204, cell2205, cell2206, cell2207]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275


