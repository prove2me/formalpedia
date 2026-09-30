-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0274
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0274
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:51:08.039349+00:00
-- url     : https://prove2.me/theorems/4a8981e8-386d-4871-b28f-325bdf1c0626
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0274.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0274_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2197 : work2197.theta.ok = true ∧
    work2197.jac.invOK = true ∧ acceptsUnitSq work2197.out = true := by decide +kernel

def cell2197 : CellCertificate where
  tauBall := tau2197
  contactCenter := center2197
  contactBall := contact2197
  work := work2197
  center_sq := center_sq2197
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2197.1
  jac_ok := checks2197.2.1
  accepted := checks2197.2.2

def tau2198 : RatBall :=
  ⟨⟨-7/320, 113/320⟩, 3/640⟩
def center2198 : GaussianRat :=
  ⟨-17410471/1000000000, 51215337/200000000⟩
def contact2198 : RatBall := localContactBall tau2198 center2198
def work2198 : RoundedTauEval :=
  evalTau precision tau2198 contact2198 logTwoBall

theorem center_sq2198 : (center2198.re : ℝ)^2 +
    (center2198.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2198]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2198 : work2198.theta.ok = true ∧
    work2198.jac.invOK = true ∧ acceptsUnitSq work2198.out = true := by decide +kernel

def cell2198 : CellCertificate where
  tauBall := tau2198
  contactCenter := center2198
  contactBall := contact2198
  work := work2198
  center_sq := center_sq2198
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2198.1
  jac_ok := checks2198.2.1
  accepted := checks2198.2.2

def tau2199 : RatBall :=
  ⟨⟨-1/64, 113/320⟩, 3/640⟩
def center2199 : GaussianRat :=
  ⟨-12437881/1000000000, 3201937/12500000⟩
def contact2199 : RatBall := localContactBall tau2199 center2199
def work2199 : RoundedTauEval :=
  evalTau precision tau2199 contact2199 logTwoBall

theorem center_sq2199 : (center2199.re : ℝ)^2 +
    (center2199.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2199]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2199 : work2199.theta.ok = true ∧
    work2199.jac.invOK = true ∧ acceptsUnitSq work2199.out = true := by decide +kernel

def cell2199 : CellCertificate where
  tauBall := tau2199
  contactCenter := center2199
  contactBall := contact2199
  work := work2199
  center_sq := center_sq2199
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2199.1
  jac_ok := checks2199.2.1
  accepted := checks2199.2.2

def cells : List CellCertificate := [cell2192, cell2193, cell2194, cell2195, cell2196, cell2197, cell2198, cell2199]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274


