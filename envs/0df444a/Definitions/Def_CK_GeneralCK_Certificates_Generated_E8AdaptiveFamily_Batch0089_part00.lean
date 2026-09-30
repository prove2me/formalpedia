-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0089_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0089_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:13:50.4894+00:00
-- url     : https://prove2.me/theorems/3e234c07-a1aa-491d-84b4-80c59e5842f4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0089 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0712 : RatBall :=
  ⟨⟨51/160, -31/160⟩, 3/320⟩
def center0712 : GaussianRat :=
  ⟨110447247/500000000, -61169673/500000000⟩
def contact0712 : RatBall := localContactBall tau0712 center0712
def work0712 : RoundedTauEval :=
  evalTau precision tau0712 contact0712 logTwoBall

theorem center_sq0712 : (center0712.re : ℝ)^2 +
    (center0712.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0712]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0712 : work0712.theta.ok = true ∧
    work0712.jac.invOK = true ∧ acceptsUnitSq work0712.out = true := by decide +kernel

def cell0712 : CellCertificate where
  tauBall := tau0712
  contactCenter := center0712
  contactBall := contact0712
  work := work0712
  center_sq := center_sq0712
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0712.1
  jac_ok := checks0712.2.1
  accepted := checks0712.2.2

def tau0713 : RatBall :=
  ⟨⟨49/160, -29/160⟩, 3/320⟩
def center0713 : GaussianRat :=
  ⟨52985469/250000000, -115229173/1000000000⟩
def contact0713 : RatBall := localContactBall tau0713 center0713
def work0713 : RoundedTauEval :=
  evalTau precision tau0713 contact0713 logTwoBall

theorem center_sq0713 : (center0713.re : ℝ)^2 +
    (center0713.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0713]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0713 : work0713.theta.ok = true ∧
    work0713.jac.invOK = true ∧ acceptsUnitSq work0713.out = true := by decide +kernel

def cell0713 : CellCertificate where
  tauBall := tau0713
  contactCenter := center0713
  contactBall := contact0713
  work := work0713
  center_sq := center_sq0713
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0713.1
  jac_ok := checks0713.2.1
  accepted := checks0713.2.2

def tau0714 : RatBall :=
  ⟨⟨51/160, -29/160⟩, 3/320⟩
def center0714 : GaussianRat :=
  ⟨429614/1953125, -114341983/1000000000⟩
def contact0714 : RatBall := localContactBall tau0714 center0714
def work0714 : RoundedTauEval :=
  evalTau precision tau0714 contact0714 logTwoBall

theorem center_sq0714 : (center0714.re : ℝ)^2 +
    (center0714.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0714]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0714 : work0714.theta.ok = true ∧
    work0714.jac.invOK = true ∧ acceptsUnitSq work0714.out = true := by decide +kernel

def cell0714 : CellCertificate where
  tauBall := tau0714
  contactCenter := center0714
  contactBall := contact0714
  work := work0714
  center_sq := center_sq0714
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0714.1
  jac_ok := checks0714.2.1
  accepted := checks0714.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089


