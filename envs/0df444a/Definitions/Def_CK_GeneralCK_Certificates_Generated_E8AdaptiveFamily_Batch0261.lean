-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0261
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0261
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:53:12.209834+00:00
-- url     : https://prove2.me/theorems/5d87cb1c-5c18-4230-b0c4-0ace99bf8bd2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0261.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0261_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2093 : work2093.theta.ok = true ∧
    work2093.jac.invOK = true ∧ acceptsUnitSq work2093.out = true := by decide +kernel

def cell2093 : CellCertificate where
  tauBall := tau2093
  contactCenter := center2093
  contactBall := contact2093
  work := work2093
  center_sq := center_sq2093
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2093.1
  jac_ok := checks2093.2.1
  accepted := checks2093.2.2

def tau2094 : RatBall :=
  ⟨⟨-9/64, 109/320⟩, 3/640⟩
def center2094 : GaussianRat :=
  ⟨-109524891/1000000000, 240262931/1000000000⟩
def contact2094 : RatBall := localContactBall tau2094 center2094
def work2094 : RoundedTauEval :=
  evalTau precision tau2094 contact2094 logTwoBall

theorem center_sq2094 : (center2094.re : ℝ)^2 +
    (center2094.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2094]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2094 : work2094.theta.ok = true ∧
    work2094.jac.invOK = true ∧ acceptsUnitSq work2094.out = true := by decide +kernel

def cell2094 : CellCertificate where
  tauBall := tau2094
  contactCenter := center2094
  contactBall := contact2094
  work := work2094
  center_sq := center_sq2094
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2094.1
  jac_ok := checks2094.2.1
  accepted := checks2094.2.2

def tau2095 : RatBall :=
  ⟨⟨-47/320, 111/320⟩, 3/640⟩
def center2095 : GaussianRat :=
  ⟨-57413127/500000000, 244479579/1000000000⟩
def contact2095 : RatBall := localContactBall tau2095 center2095
def work2095 : RoundedTauEval :=
  evalTau precision tau2095 contact2095 logTwoBall

theorem center_sq2095 : (center2095.re : ℝ)^2 +
    (center2095.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2095]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2095 : work2095.theta.ok = true ∧
    work2095.jac.invOK = true ∧ acceptsUnitSq work2095.out = true := by decide +kernel

def cell2095 : CellCertificate where
  tauBall := tau2095
  contactCenter := center2095
  contactBall := contact2095
  work := work2095
  center_sq := center_sq2095
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2095.1
  jac_ok := checks2095.2.1
  accepted := checks2095.2.2

def cells : List CellCertificate := [cell2088, cell2089, cell2090, cell2091, cell2092, cell2093, cell2094, cell2095]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261


