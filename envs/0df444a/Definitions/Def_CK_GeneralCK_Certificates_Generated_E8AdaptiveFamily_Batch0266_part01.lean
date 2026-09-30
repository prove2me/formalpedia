-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0266_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0266_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:33:33.694399+00:00
-- url     : https://prove2.me/theorems/71853913-1d7f-4494-bd00-af7d11056baf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0266 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0266_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2132 : RatBall :=
  ⟨⟨-37/320, 117/320⟩, 3/640⟩
def center2132 : GaussianRat :=
  ⟨-46124689/500000000, 261610997/1000000000⟩
def contact2132 : RatBall := localContactBall tau2132 center2132
def work2132 : RoundedTauEval :=
  evalTau precision tau2132 contact2132 logTwoBall

theorem center_sq2132 : (center2132.re : ℝ)^2 +
    (center2132.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2132]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2132 : work2132.theta.ok = true ∧
    work2132.jac.invOK = true ∧ acceptsUnitSq work2132.out = true := by decide +kernel

def cell2132 : CellCertificate where
  tauBall := tau2132
  contactCenter := center2132
  contactBall := contact2132
  work := work2132
  center_sq := center_sq2132
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2132.1
  jac_ok := checks2132.2.1
  accepted := checks2132.2.2

def tau2133 : RatBall :=
  ⟨⟨-7/64, 117/320⟩, 3/640⟩
def center2133 : GaussianRat :=
  ⟨-43670547/500000000, 65522293/250000000⟩
def contact2133 : RatBall := localContactBall tau2133 center2133
def work2133 : RoundedTauEval :=
  evalTau precision tau2133 contact2133 logTwoBall

theorem center_sq2133 : (center2133.re : ℝ)^2 +
    (center2133.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2133]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2133 : work2133.theta.ok = true ∧
    work2133.jac.invOK = true ∧ acceptsUnitSq work2133.out = true := by decide +kernel

def cell2133 : CellCertificate where
  tauBall := tau2133
  contactCenter := center2133
  contactBall := contact2133
  work := work2133
  center_sq := center_sq2133
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2133.1
  jac_ok := checks2133.2.1
  accepted := checks2133.2.2

def tau2134 : RatBall :=
  ⟨⟨-33/320, 117/320⟩, 3/640⟩
def center2134 : GaussianRat :=
  ⟨-1648401/20000000, 65635667/250000000⟩
def contact2134 : RatBall := localContactBall tau2134 center2134
def work2134 : RoundedTauEval :=
  evalTau precision tau2134 contact2134 logTwoBall

theorem center_sq2134 : (center2134.re : ℝ)^2 +
    (center2134.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2134]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2134 : work2134.theta.ok = true ∧
    work2134.jac.invOK = true ∧ acceptsUnitSq work2134.out = true := by decide +kernel

def cell2134 : CellCertificate where
  tauBall := tau2134
  contactCenter := center2134
  contactBall := contact2134
  work := work2134
  center_sq := center_sq2134
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2134.1
  jac_ok := checks2134.2.1
  accepted := checks2134.2.2

def tau2135 : RatBall :=
  ⟨⟨-31/320, 109/320⟩, 3/640⟩
def center2135 : GaussianRat :=
  ⟨-75911827/1000000000, 121705269/500000000⟩
def contact2135 : RatBall := localContactBall tau2135 center2135
def work2135 : RoundedTauEval :=
  evalTau precision tau2135 contact2135 logTwoBall

theorem center_sq2135 : (center2135.re : ℝ)^2 +
    (center2135.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2135]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2135 : work2135.theta.ok = true ∧
    work2135.jac.invOK = true ∧ acceptsUnitSq work2135.out = true := by decide +kernel

def cell2135 : CellCertificate where
  tauBall := tau2135
  contactCenter := center2135
  contactBall := contact2135
  work := work2135
  center_sq := center_sq2135
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2135.1
  jac_ok := checks2135.2.1
  accepted := checks2135.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266


