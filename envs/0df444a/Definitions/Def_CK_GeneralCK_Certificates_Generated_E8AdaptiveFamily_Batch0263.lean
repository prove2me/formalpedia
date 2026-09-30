-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0263
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0263
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:51:49.775117+00:00
-- url     : https://prove2.me/theorems/e4fe2a0f-f735-4e03-a0ee-27ca97a850c5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0263.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0263_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2109 : (center2109.re : ℝ)^2 +
    (center2109.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2109]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2109 : work2109.theta.ok = true ∧
    work2109.jac.invOK = true ∧ acceptsUnitSq work2109.out = true := by decide +kernel

def cell2109 : CellCertificate where
  tauBall := tau2109
  contactCenter := center2109
  contactBall := contact2109
  work := work2109
  center_sq := center_sq2109
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2109.1
  jac_ok := checks2109.2.1
  accepted := checks2109.2.2

def tau2110 : RatBall :=
  ⟨⟨-33/320, 109/320⟩, 3/640⟩
def center2110 : GaussianRat :=
  ⟨-20187397/250000000, 48605377/200000000⟩
def contact2110 : RatBall := localContactBall tau2110 center2110
def work2110 : RoundedTauEval :=
  evalTau precision tau2110 contact2110 logTwoBall

theorem center_sq2110 : (center2110.re : ℝ)^2 +
    (center2110.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2110]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2110 : work2110.theta.ok = true ∧
    work2110.jac.invOK = true ∧ acceptsUnitSq work2110.out = true := by decide +kernel

def cell2110 : CellCertificate where
  tauBall := tau2110
  contactCenter := center2110
  contactBall := contact2110
  work := work2110
  center_sq := center_sq2110
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2110.1
  jac_ok := checks2110.2.1
  accepted := checks2110.2.2

def tau2111 : RatBall :=
  ⟨⟨-7/64, 111/320⟩, 3/640⟩
def center2111 : GaussianRat :=
  ⟨-85999463/1000000000, 247453051/1000000000⟩
def contact2111 : RatBall := localContactBall tau2111 center2111
def work2111 : RoundedTauEval :=
  evalTau precision tau2111 contact2111 logTwoBall

theorem center_sq2111 : (center2111.re : ℝ)^2 +
    (center2111.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2111]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2111 : work2111.theta.ok = true ∧
    work2111.jac.invOK = true ∧ acceptsUnitSq work2111.out = true := by decide +kernel

def cell2111 : CellCertificate where
  tauBall := tau2111
  contactCenter := center2111
  contactBall := contact2111
  work := work2111
  center_sq := center_sq2111
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2111.1
  jac_ok := checks2111.2.1
  accepted := checks2111.2.2

def cells : List CellCertificate := [cell2104, cell2105, cell2106, cell2107, cell2108, cell2109, cell2110, cell2111]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263


