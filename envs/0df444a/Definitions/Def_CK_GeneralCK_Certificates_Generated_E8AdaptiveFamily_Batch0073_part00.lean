-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0073_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0073_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:55:19.368462+00:00
-- url     : https://prove2.me/theorems/8ab3ad4a-62f2-465c-860d-966a69966ee0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0073 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0584 : RatBall :=
  ⟨⟨13/160, -51/160⟩, 3/320⟩
def center0584 : GaussianRat :=
  ⟨2508961/40000000, -56843321/250000000⟩
def contact0584 : RatBall := localContactBall tau0584 center0584
def work0584 : RoundedTauEval :=
  evalTau precision tau0584 contact0584 logTwoBall

theorem center_sq0584 : (center0584.re : ℝ)^2 +
    (center0584.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0584]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0584 : work0584.theta.ok = true ∧
    work0584.jac.invOK = true ∧ acceptsUnitSq work0584.out = true := by decide +kernel

def cell0584 : CellCertificate where
  tauBall := tau0584
  contactCenter := center0584
  contactBall := contact0584
  work := work0584
  center_sq := center_sq0584
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0584.1
  jac_ok := checks0584.2.1
  accepted := checks0584.2.2

def tau0585 : RatBall :=
  ⟨⟨3/32, -51/160⟩, 3/320⟩
def center0585 : GaussianRat :=
  ⟨18071427/250000000, -113380411/500000000⟩
def contact0585 : RatBall := localContactBall tau0585 center0585
def work0585 : RoundedTauEval :=
  evalTau precision tau0585 contact0585 logTwoBall

theorem center_sq0585 : (center0585.re : ℝ)^2 +
    (center0585.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0585]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0585 : work0585.theta.ok = true ∧
    work0585.jac.invOK = true ∧ acceptsUnitSq work0585.out = true := by decide +kernel

def cell0585 : CellCertificate where
  tauBall := tau0585
  contactCenter := center0585
  contactBall := contact0585
  work := work0585
  center_sq := center_sq0585
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0585.1
  jac_ok := checks0585.2.1
  accepted := checks0585.2.2

def tau0586 : RatBall :=
  ⟨⟨13/160, -49/160⟩, 3/320⟩
def center0586 : GaussianRat :=
  ⟨3885599/62500000, -6807377/31250000⟩
def contact0586 : RatBall := localContactBall tau0586 center0586
def work0586 : RoundedTauEval :=
  evalTau precision tau0586 contact0586 logTwoBall

theorem center_sq0586 : (center0586.re : ℝ)^2 +
    (center0586.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0586]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0586 : work0586.theta.ok = true ∧
    work0586.jac.invOK = true ∧ acceptsUnitSq work0586.out = true := by decide +kernel

def cell0586 : CellCertificate where
  tauBall := tau0586
  contactCenter := center0586
  contactBall := contact0586
  work := work0586
  center_sq := center_sq0586
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0586.1
  jac_ok := checks0586.2.1
  accepted := checks0586.2.2

def tau0587 : RatBall :=
  ⟨⟨3/32, -49/160⟩, 3/320⟩
def center0587 : GaussianRat :=
  ⟨14329959/200000000, -108628837/500000000⟩
def contact0587 : RatBall := localContactBall tau0587 center0587
def work0587 : RoundedTauEval :=
  evalTau precision tau0587 contact0587 logTwoBall

theorem center_sq0587 : (center0587.re : ℝ)^2 +
    (center0587.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0587]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0587 : work0587.theta.ok = true ∧
    work0587.jac.invOK = true ∧ acceptsUnitSq work0587.out = true := by decide +kernel

def cell0587 : CellCertificate where
  tauBall := tau0587
  contactCenter := center0587
  contactBall := contact0587
  work := work0587
  center_sq := center_sq0587
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0587.1
  jac_ok := checks0587.2.1
  accepted := checks0587.2.2

def tau0588 : RatBall :=
  ⟨⟨17/160, -53/160⟩, 3/320⟩
def center0588 : GaussianRat :=
  ⟨82567747/1000000000, -117805603/500000000⟩
def contact0588 : RatBall := localContactBall tau0588 center0588
def work0588 : RoundedTauEval :=
  evalTau precision tau0588 contact0588 logTwoBall

theorem center_sq0588 : (center0588.re : ℝ)^2 +
    (center0588.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0588]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0588 : work0588.theta.ok = true ∧
    work0588.jac.invOK = true ∧ acceptsUnitSq work0588.out = true := by decide +kernel

def cell0588 : CellCertificate where
  tauBall := tau0588
  contactCenter := center0588
  contactBall := contact0588
  work := work0588
  center_sq := center_sq0588
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0588.1
  jac_ok := checks0588.2.1
  accepted := checks0588.2.2

def tau0589 : RatBall :=
  ⟨⟨17/160, -51/160⟩, 3/320⟩
def center0589 : GaussianRat :=
  ⟨40905123/500000000, -113032697/500000000⟩
def contact0589 : RatBall := localContactBall tau0589 center0589
def work0589 : RoundedTauEval :=
  evalTau precision tau0589 contact0589 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073


