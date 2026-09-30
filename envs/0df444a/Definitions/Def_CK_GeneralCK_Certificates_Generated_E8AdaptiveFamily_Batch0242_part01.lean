-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0242_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0242_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:10:28.13065+00:00
-- url     : https://prove2.me/theorems/ef625cd1-869e-4bdc-affd-4478e91bca17
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 2 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 2 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 2 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 2 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0242 (part 2 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0242_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1938 : RatBall :=
  ⟨⟨-91/320, 89/320⟩, 3/640⟩
def center1938 : GaussianRat :=
  ⟨-103128439/500000000, 180903081/1000000000⟩
def contact1938 : RatBall := localContactBall tau1938 center1938
def work1938 : RoundedTauEval :=
  evalTau precision tau1938 contact1938 logTwoBall

theorem center_sq1938 : (center1938.re : ℝ)^2 +
    (center1938.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1938]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1938 : work1938.theta.ok = true ∧
    work1938.jac.invOK = true ∧ acceptsUnitSq work1938.out = true := by decide +kernel

def cell1938 : CellCertificate where
  tauBall := tau1938
  contactCenter := center1938
  contactBall := contact1938
  work := work1938
  center_sq := center_sq1938
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1938.1
  jac_ok := checks1938.2.1
  accepted := checks1938.2.2

def tau1939 : RatBall :=
  ⟨⟨-89/320, 89/320⟩, 3/640⟩
def center1939 : GaussianRat :=
  ⟨-40408359/200000000, 181587727/1000000000⟩
def contact1939 : RatBall := localContactBall tau1939 center1939
def work1939 : RoundedTauEval :=
  evalTau precision tau1939 contact1939 logTwoBall

theorem center_sq1939 : (center1939.re : ℝ)^2 +
    (center1939.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1939]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1939 : work1939.theta.ok = true ∧
    work1939.jac.invOK = true ∧ acceptsUnitSq work1939.out = true := by decide +kernel

def cell1939 : CellCertificate where
  tauBall := tau1939
  contactCenter := center1939
  contactBall := contact1939
  work := work1939
  center_sq := center_sq1939
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1939.1
  jac_ok := checks1939.2.1
  accepted := checks1939.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242


