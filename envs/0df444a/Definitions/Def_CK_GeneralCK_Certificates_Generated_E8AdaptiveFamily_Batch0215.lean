-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0215
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0215
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:48:09.919992+00:00
-- url     : https://prove2.me/theorems/faf3e216-8b37-49ed-ae45-415b60c444f0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0215.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0215_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1724 : RoundedTauEval :=
  evalTau precision tau1724 contact1724 logTwoBall

theorem center_sq1724 : (center1724.re : ℝ)^2 +
    (center1724.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1724]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1724 : work1724.theta.ok = true ∧
    work1724.jac.invOK = true ∧ acceptsUnitSq work1724.out = true := by decide +kernel

def cell1724 : CellCertificate where
  tauBall := tau1724
  contactCenter := center1724
  contactBall := contact1724
  work := work1724
  center_sq := center_sq1724
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1724.1
  jac_ok := checks1724.2.1
  accepted := checks1724.2.2

def tau1725 : RatBall :=
  ⟨⟨61/320, -103/320⟩, 3/640⟩
def center1725 : GaussianRat :=
  ⟨5804463/40000000, -221637027/1000000000⟩
def contact1725 : RatBall := localContactBall tau1725 center1725
def work1725 : RoundedTauEval :=
  evalTau precision tau1725 contact1725 logTwoBall

theorem center_sq1725 : (center1725.re : ℝ)^2 +
    (center1725.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1725]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1725 : work1725.theta.ok = true ∧
    work1725.jac.invOK = true ∧ acceptsUnitSq work1725.out = true := by decide +kernel

def cell1725 : CellCertificate where
  tauBall := tau1725
  contactCenter := center1725
  contactBall := contact1725
  work := work1725
  center_sq := center_sq1725
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1725.1
  jac_ok := checks1725.2.1
  accepted := checks1725.2.2

def tau1726 : RatBall :=
  ⟨⟨63/320, -103/320⟩, 3/640⟩
def center1726 : GaussianRat :=
  ⟨74838049/500000000, -221002847/1000000000⟩
def contact1726 : RatBall := localContactBall tau1726 center1726
def work1726 : RoundedTauEval :=
  evalTau precision tau1726 contact1726 logTwoBall

theorem center_sq1726 : (center1726.re : ℝ)^2 +
    (center1726.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1726]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1726 : work1726.theta.ok = true ∧
    work1726.jac.invOK = true ∧ acceptsUnitSq work1726.out = true := by decide +kernel

def cell1726 : CellCertificate where
  tauBall := tau1726
  contactCenter := center1726
  contactBall := contact1726
  work := work1726
  center_sq := center_sq1726
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1726.1
  jac_ok := checks1726.2.1
  accepted := checks1726.2.2

def tau1727 : RatBall :=
  ⟨⟨61/320, -101/320⟩, 3/640⟩
def center1727 : GaussianRat :=
  ⟨7224707/50000000, -217072079/1000000000⟩
def contact1727 : RatBall := localContactBall tau1727 center1727
def work1727 : RoundedTauEval :=
  evalTau precision tau1727 contact1727 logTwoBall

theorem center_sq1727 : (center1727.re : ℝ)^2 +
    (center1727.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1727]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1727 : work1727.theta.ok = true ∧
    work1727.jac.invOK = true ∧ acceptsUnitSq work1727.out = true := by decide +kernel

def cell1727 : CellCertificate where
  tauBall := tau1727
  contactCenter := center1727
  contactBall := contact1727
  work := work1727
  center_sq := center_sq1727
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1727.1
  jac_ok := checks1727.2.1
  accepted := checks1727.2.2

def cells : List CellCertificate := [cell1720, cell1721, cell1722, cell1723, cell1724, cell1725, cell1726, cell1727]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215


