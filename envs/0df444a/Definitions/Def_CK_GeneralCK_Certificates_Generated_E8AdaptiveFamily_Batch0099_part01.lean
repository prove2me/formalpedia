-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0099_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0099_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:20:00.059072+00:00
-- url     : https://prove2.me/theorems/92b6e545-4ac1-4669-b277-e9fca79dc6ff
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0099 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0099_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0795 : RatBall :=
  ⟨⟨-61/160, 23/160⟩, 3/320⟩
def center0795 : GaussianRat :=
  ⟨-64096843/250000000, 86787913/1000000000⟩
def contact0795 : RatBall := localContactBall tau0795 center0795
def work0795 : RoundedTauEval :=
  evalTau precision tau0795 contact0795 logTwoBall

theorem center_sq0795 : (center0795.re : ℝ)^2 +
    (center0795.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0795]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0795 : work0795.theta.ok = true ∧
    work0795.jac.invOK = true ∧ acceptsUnitSq work0795.out = true := by decide +kernel

def cell0795 : CellCertificate where
  tauBall := tau0795
  contactCenter := center0795
  contactBall := contact0795
  work := work0795
  center_sq := center_sq0795
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0795.1
  jac_ok := checks0795.2.1
  accepted := checks0795.2.2

def tau0796 : RatBall :=
  ⟨⟨-59/160, 21/160⟩, 3/320⟩
def center0796 : GaussianRat :=
  ⟨-124018963/500000000, 79895753/1000000000⟩
def contact0796 : RatBall := localContactBall tau0796 center0796
def work0796 : RoundedTauEval :=
  evalTau precision tau0796 contact0796 logTwoBall

theorem center_sq0796 : (center0796.re : ℝ)^2 +
    (center0796.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0796]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0796 : work0796.theta.ok = true ∧
    work0796.jac.invOK = true ∧ acceptsUnitSq work0796.out = true := by decide +kernel

def cell0796 : CellCertificate where
  tauBall := tau0796
  contactCenter := center0796
  contactBall := contact0796
  work := work0796
  center_sq := center_sq0796
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0796.1
  jac_ok := checks0796.2.1
  accepted := checks0796.2.2

def tau0797 : RatBall :=
  ⟨⟨-57/160, 21/160⟩, 3/320⟩
def center0797 : GaussianRat :=
  ⟨-120177071/500000000, 16115617/200000000⟩
def contact0797 : RatBall := localContactBall tau0797 center0797
def work0797 : RoundedTauEval :=
  evalTau precision tau0797 contact0797 logTwoBall

theorem center_sq0797 : (center0797.re : ℝ)^2 +
    (center0797.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0797]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0797 : work0797.theta.ok = true ∧
    work0797.jac.invOK = true ∧ acceptsUnitSq work0797.out = true := by decide +kernel

def cell0797 : CellCertificate where
  tauBall := tau0797
  contactCenter := center0797
  contactBall := contact0797
  work := work0797
  center_sq := center_sq0797
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0797.1
  jac_ok := checks0797.2.1
  accepted := checks0797.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099


