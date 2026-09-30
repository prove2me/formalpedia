-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0042_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0042_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:27:08.93211+00:00
-- url     : https://prove2.me/theorems/5ae934f2-fc2f-4860-9d63-d329c73fcdc2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0042 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0042_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center0339 : GaussianRat :=
  ⟨24798221/250000000, 36637923/250000000⟩
def contact0339 : RatBall := localContactBall tau0339 center0339
def work0339 : RoundedTauEval :=
  evalTau precision tau0339 contact0339 logTwoBall

theorem center_sq0339 : (center0339.re : ℝ)^2 +
    (center0339.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0339]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0339 : work0339.theta.ok = true ∧
    work0339.jac.invOK = true ∧ acceptsUnitSq work0339.out = true := by decide +kernel

def cell0339 : CellCertificate where
  tauBall := tau0339
  contactCenter := center0339
  contactBall := contact0339
  work := work0339
  center_sq := center_sq0339
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0339.1
  jac_ok := checks0339.2.1
  accepted := checks0339.2.2

def tau0340 : RatBall :=
  ⟨⟨9/80, 19/80⟩, 3/160⟩
def center0340 : GaussianRat :=
  ⟨20589547/250000000, 33110861/200000000⟩
def contact0340 : RatBall := localContactBall tau0340 center0340
def work0340 : RoundedTauEval :=
  evalTau precision tau0340 contact0340 logTwoBall

theorem center_sq0340 : (center0340.re : ℝ)^2 +
    (center0340.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0340]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0340 : work0340.theta.ok = true ∧
    work0340.jac.invOK = true ∧ acceptsUnitSq work0340.out = true := by decide +kernel

def cell0340 : CellCertificate where
  tauBall := tau0340
  contactCenter := center0340
  contactBall := contact0340
  work := work0340
  center_sq := center_sq0340
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0340.1
  jac_ok := checks0340.2.1
  accepted := checks0340.2.2

def tau0341 : RatBall :=
  ⟨⟨11/80, 19/80⟩, 3/160⟩
def center0341 : GaussianRat :=
  ⟨25094739/250000000, 82197279/500000000⟩
def contact0341 : RatBall := localContactBall tau0341 center0341
def work0341 : RoundedTauEval :=
  evalTau precision tau0341 contact0341 logTwoBall

theorem center_sq0341 : (center0341.re : ℝ)^2 +
    (center0341.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0341]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0341 : work0341.theta.ok = true ∧
    work0341.jac.invOK = true ∧ acceptsUnitSq work0341.out = true := by decide +kernel

def cell0341 : CellCertificate where
  tauBall := tau0341
  contactCenter := center0341
  contactBall := contact0341
  work := work0341
  center_sq := center_sq0341
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0341.1
  jac_ok := checks0341.2.1
  accepted := checks0341.2.2

def tau0342 : RatBall :=
  ⟨⟨13/80, 17/80⟩, 3/160⟩
def center0342 : GaussianRat :=
  ⟨58429249/500000000, 145353777/1000000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042


