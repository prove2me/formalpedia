-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0069_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0069_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:06:09.649811+00:00
-- url     : https://prove2.me/theorems/0fab2923-9600-49f5-a5e1-2e7243f995eb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0069 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0552 : RatBall :=
  ⟨⟨-63/160, -9/160⟩, 3/320⟩
def center0552 : GaussianRat :=
  ⟨-65046299/250000000, -6715607/200000000⟩
def contact0552 : RatBall := localContactBall tau0552 center0552
def work0552 : RoundedTauEval :=
  evalTau precision tau0552 contact0552 logTwoBall

theorem center_sq0552 : (center0552.re : ℝ)^2 +
    (center0552.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0552]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0552 : work0552.theta.ok = true ∧
    work0552.jac.invOK = true ∧ acceptsUnitSq work0552.out = true := by decide +kernel

def cell0552 : CellCertificate where
  tauBall := tau0552
  contactCenter := center0552
  contactBall := contact0552
  work := work0552
  center_sq := center_sq0552
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0552.1
  jac_ok := checks0552.2.1
  accepted := checks0552.2.2

def tau0553 : RatBall :=
  ⟨⟨-61/160, -9/160⟩, 3/320⟩
def center0553 : GaussianRat :=
  ⟨-252683709/1000000000, -6774897/200000000⟩
def contact0553 : RatBall := localContactBall tau0553 center0553
def work0553 : RoundedTauEval :=
  evalTau precision tau0553 contact0553 logTwoBall

theorem center_sq0553 : (center0553.re : ℝ)^2 +
    (center0553.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0553]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0553 : work0553.theta.ok = true ∧
    work0553.jac.invOK = true ∧ acceptsUnitSq work0553.out = true := by decide +kernel

def cell0553 : CellCertificate where
  tauBall := tau0553
  contactCenter := center0553
  contactBall := contact0553
  work := work0553
  center_sq := center_sq0553
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0553.1
  jac_ok := checks0553.2.1
  accepted := checks0553.2.2

def tau0554 : RatBall :=
  ⟨⟨-63/160, -7/160⟩, 3/320⟩
def center0554 : GaussianRat :=
  ⟨-64979987/250000000, -3263977/125000000⟩
def contact0554 : RatBall := localContactBall tau0554 center0554
def work0554 : RoundedTauEval :=
  evalTau precision tau0554 contact0554 logTwoBall

theorem center_sq0554 : (center0554.re : ℝ)^2 +
    (center0554.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0554]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0554 : work0554.theta.ok = true ∧
    work0554.jac.invOK = true ∧ acceptsUnitSq work0554.out = true := by decide +kernel

def cell0554 : CellCertificate where
  tauBall := tau0554
  contactCenter := center0554
  contactBall := contact0554
  work := work0554
  center_sq := center_sq0554
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0554.1
  jac_ok := checks0554.2.1
  accepted := checks0554.2.2

def tau0555 : RatBall :=
  ⟨⟨-61/160, -7/160⟩, 3/320⟩
def center0555 : GaussianRat :=
  ⟨-252422417/1000000000, -13171007/500000000⟩
def contact0555 : RatBall := localContactBall tau0555 center0555
def work0555 : RoundedTauEval :=
  evalTau precision tau0555 contact0555 logTwoBall

theorem center_sq0555 : (center0555.re : ℝ)^2 +
    (center0555.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0555]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0555 : work0555.theta.ok = true ∧
    work0555.jac.invOK = true ∧ acceptsUnitSq work0555.out = true := by decide +kernel

def cell0555 : CellCertificate where
  tauBall := tau0555
  contactCenter := center0555
  contactBall := contact0555
  work := work0555
  center_sq := center_sq0555
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0555.1
  jac_ok := checks0555.2.1
  accepted := checks0555.2.2

def tau0556 : RatBall :=
  ⟨⟨-63/160, -1/32⟩, 3/320⟩
def center0556 : GaussianRat :=
  ⟨-259721291/1000000000, -466223/25000000⟩
def contact0556 : RatBall := localContactBall tau0556 center0556
def work0556 : RoundedTauEval :=
  evalTau precision tau0556 contact0556 logTwoBall

theorem center_sq0556 : (center0556.re : ℝ)^2 +
    (center0556.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0556]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0556 : work0556.theta.ok = true ∧
    work0556.jac.invOK = true ∧ acceptsUnitSq work0556.out = true := by decide +kernel

def cell0556 : CellCertificate where
  tauBall := tau0556
  contactCenter := center0556
  contactBall := contact0556
  work := work0556
  center_sq := center_sq0556
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0556.1
  jac_ok := checks0556.2.1
  accepted := checks0556.2.2

def tau0557 : RatBall :=
  ⟨⟨-61/160, -1/32⟩, 3/320⟩
def center0557 : GaussianRat :=
  ⟨-25222673/100000000, -18813147/1000000000⟩
def contact0557 : RatBall := localContactBall tau0557 center0557

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069


