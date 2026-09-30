-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0271
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0271
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:28:16.042474+00:00
-- url     : https://prove2.me/theorems/6e8538d9-45f5-4751-bc28-fb88f5db10f8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0271` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0271` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0271` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0271 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0271.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0271_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0271

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2174 : (center2174.re : ℝ)^2 +
    (center2174.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2174]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2174 : work2174.theta.ok = true ∧
    work2174.jac.invOK = true ∧ acceptsUnitSq work2174.out = true := by decide +kernel

def cell2174 : CellCertificate where
  tauBall := tau2174
  contactCenter := center2174
  contactBall := contact2174
  work := work2174
  center_sq := center_sq2174
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2174.1
  jac_ok := checks2174.2.1
  accepted := checks2174.2.2

def tau2175 : RatBall :=
  ⟨⟨-19/320, 117/320⟩, 3/640⟩
def center2175 : GaussianRat :=
  ⟨-23835959/500000000, 265001899/1000000000⟩
def contact2175 : RatBall := localContactBall tau2175 center2175
def work2175 : RoundedTauEval :=
  evalTau precision tau2175 contact2175 logTwoBall

theorem center_sq2175 : (center2175.re : ℝ)^2 +
    (center2175.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2175]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2175 : work2175.theta.ok = true ∧
    work2175.jac.invOK = true ∧ acceptsUnitSq work2175.out = true := by decide +kernel

def cell2175 : CellCertificate where
  tauBall := tau2175
  contactCenter := center2175
  contactBall := contact2175
  work := work2175
  center_sq := center_sq2175
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2175.1
  jac_ok := checks2175.2.1
  accepted := checks2175.2.2

def cells : List CellCertificate := [cell2168, cell2169, cell2170, cell2171, cell2172, cell2173, cell2174, cell2175]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0271


