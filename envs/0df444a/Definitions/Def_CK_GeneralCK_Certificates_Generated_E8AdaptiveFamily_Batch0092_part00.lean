-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0092_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0092_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:16:07.512462+00:00
-- url     : https://prove2.me/theorems/08a576ff-4eff-4d51-ad42-94820e5da520
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0092 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0736 : RatBall :=
  ⟨⟨53/160, -23/160⟩, 3/320⟩
def center0736 : GaussianRat :=
  ⟨225467593/1000000000, -89762261/1000000000⟩
def contact0736 : RatBall := localContactBall tau0736 center0736
def work0736 : RoundedTauEval :=
  evalTau precision tau0736 contact0736 logTwoBall

theorem center_sq0736 : (center0736.re : ℝ)^2 +
    (center0736.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0736]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0736 : work0736.theta.ok = true ∧
    work0736.jac.invOK = true ∧ acceptsUnitSq work0736.out = true := by decide +kernel

def cell0736 : CellCertificate where
  tauBall := tau0736
  contactCenter := center0736
  contactBall := contact0736
  work := work0736
  center_sq := center_sq0736
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0736.1
  jac_ok := checks0736.2.1
  accepted := checks0736.2.2

def tau0737 : RatBall :=
  ⟨⟨11/32, -23/160⟩, 3/320⟩
def center0737 : GaussianRat :=
  ⟨58324897/250000000, -11129939/125000000⟩
def contact0737 : RatBall := localContactBall tau0737 center0737
def work0737 : RoundedTauEval :=
  evalTau precision tau0737 contact0737 logTwoBall

theorem center_sq0737 : (center0737.re : ℝ)^2 +
    (center0737.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0737]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0737 : work0737.theta.ok = true ∧
    work0737.jac.invOK = true ∧ acceptsUnitSq work0737.out = true := by decide +kernel

def cell0737 : CellCertificate where
  tauBall := tau0737
  contactCenter := center0737
  contactBall := contact0737
  work := work0737
  center_sq := center_sq0737
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0737.1
  jac_ok := checks0737.2.1
  accepted := checks0737.2.2

def tau0738 : RatBall :=
  ⟨⟨53/160, -21/160⟩, 3/320⟩
def center0738 : GaussianRat :=
  ⟨224785281/1000000000, -4095231/50000000⟩
def contact0738 : RatBall := localContactBall tau0738 center0738
def work0738 : RoundedTauEval :=
  evalTau precision tau0738 contact0738 logTwoBall

theorem center_sq0738 : (center0738.re : ℝ)^2 +
    (center0738.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0738]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0738 : work0738.theta.ok = true ∧
    work0738.jac.invOK = true ∧ acceptsUnitSq work0738.out = true := by decide +kernel

def cell0738 : CellCertificate where
  tauBall := tau0738
  contactCenter := center0738
  contactBall := contact0738
  work := work0738
  center_sq := center_sq0738
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0738.1
  jac_ok := checks0738.2.1
  accepted := checks0738.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092


