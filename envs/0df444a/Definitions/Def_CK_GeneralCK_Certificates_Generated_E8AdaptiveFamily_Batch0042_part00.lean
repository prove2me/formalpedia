-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0042_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0042_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:13:46.338846+00:00
-- url     : https://prove2.me/theorems/612340e1-438b-4201-bab1-46f1666149dd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0042 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0336 : RatBall :=
  ⟨⟨1/16, 21/80⟩, 3/160⟩
def center0336 : GaussianRat :=
  ⟨46572457/1000000000, 46409673/250000000⟩
def contact0336 : RatBall := localContactBall tau0336 center0336
def work0336 : RoundedTauEval :=
  evalTau precision tau0336 contact0336 logTwoBall

theorem center_sq0336 : (center0336.re : ℝ)^2 +
    (center0336.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0336]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0336 : work0336.theta.ok = true ∧
    work0336.jac.invOK = true ∧ acceptsUnitSq work0336.out = true := by decide +kernel

def cell0336 : CellCertificate where
  tauBall := tau0336
  contactCenter := center0336
  contactBall := contact0336
  work := work0336
  center_sq := center_sq0336
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0336.1
  jac_ok := checks0336.2.1
  accepted := checks0336.2.2

def tau0337 : RatBall :=
  ⟨⟨7/80, 21/80⟩, 3/160⟩
def center0337 : GaussianRat :=
  ⟨6508393/100000000, 184829567/1000000000⟩
def contact0337 : RatBall := localContactBall tau0337 center0337
def work0337 : RoundedTauEval :=
  evalTau precision tau0337 contact0337 logTwoBall

theorem center_sq0337 : (center0337.re : ℝ)^2 +
    (center0337.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0337]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0337 : work0337.theta.ok = true ∧
    work0337.jac.invOK = true ∧ acceptsUnitSq work0337.out = true := by decide +kernel

def cell0337 : CellCertificate where
  tauBall := tau0337
  contactCenter := center0337
  contactBall := contact0337
  work := work0337
  center_sq := center_sq0337
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0337.1
  jac_ok := checks0337.2.1
  accepted := checks0337.2.2

def tau0338 : RatBall :=
  ⟨⟨9/80, 17/80⟩, 3/160⟩
def center0338 : GaussianRat :=
  ⟨4068673/50000000, 73782899/500000000⟩
def contact0338 : RatBall := localContactBall tau0338 center0338
def work0338 : RoundedTauEval :=
  evalTau precision tau0338 contact0338 logTwoBall

theorem center_sq0338 : (center0338.re : ℝ)^2 +
    (center0338.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0338]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0338 : work0338.theta.ok = true ∧
    work0338.jac.invOK = true ∧ acceptsUnitSq work0338.out = true := by decide +kernel

def cell0338 : CellCertificate where
  tauBall := tau0338
  contactCenter := center0338
  contactBall := contact0338
  work := work0338
  center_sq := center_sq0338
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0338.1
  jac_ok := checks0338.2.1
  accepted := checks0338.2.2

def tau0339 : RatBall :=
  ⟨⟨11/80, 17/80⟩, 3/160⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042


