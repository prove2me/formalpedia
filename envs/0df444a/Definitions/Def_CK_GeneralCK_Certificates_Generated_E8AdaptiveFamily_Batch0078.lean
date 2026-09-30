-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0078
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0078
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:34:34.771983+00:00
-- url     : https://prove2.me/theorems/4c27240e-0fe1-4e96-9af4-18393096517e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0078` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0078` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0078` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0078 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0078.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0078 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0078

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0624 : RatBall :=
  ⟨⟨5/32, -9/32⟩, 3/320⟩
def center0624 : GaussianRat :=
  ⟨116565793/1000000000, -194890619/1000000000⟩
def contact0624 : RatBall := localContactBall tau0624 center0624
def work0624 : RoundedTauEval :=
  evalTau precision tau0624 contact0624 logTwoBall

theorem center_sq0624 : (center0624.re : ℝ)^2 +
    (center0624.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0624]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0624 : work0624.theta.ok = true ∧
    work0624.jac.invOK = true ∧ acceptsUnitSq work0624.out = true := by decide +kernel

def cell0624 : CellCertificate where
  tauBall := tau0624
  contactCenter := center0624
  contactBall := contact0624
  work := work0624
  center_sq := center_sq0624
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0624.1
  jac_ok := checks0624.2.1
  accepted := checks0624.2.2

def tau0625 : RatBall :=
  ⟨⟨27/160, -9/32⟩, 3/320⟩
def center0625 : GaussianRat :=
  ⟨25128347/200000000, -9698989/50000000⟩
def contact0625 : RatBall := localContactBall tau0625 center0625
def work0625 : RoundedTauEval :=
  evalTau precision tau0625 contact0625 logTwoBall

theorem center_sq0625 : (center0625.re : ℝ)^2 +
    (center0625.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0625]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0625 : work0625.theta.ok = true ∧
    work0625.jac.invOK = true ∧ acceptsUnitSq work0625.out = true := by decide +kernel

def cell0625 : CellCertificate where
  tauBall := tau0625
  contactCenter := center0625
  contactBall := contact0625
  work := work0625
  center_sq := center_sq0625
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0625.1
  jac_ok := checks0625.2.1
  accepted := checks0625.2.2

def tau0626 : RatBall :=
  ⟨⟨29/160, -47/160⟩, 3/320⟩
def center0626 : GaussianRat :=
  ⟨135691941/1000000000, -202030811/1000000000⟩
def contact0626 : RatBall := localContactBall tau0626 center0626
def work0626 : RoundedTauEval :=
  evalTau precision tau0626 contact0626 logTwoBall

theorem center_sq0626 : (center0626.re : ℝ)^2 +
    (center0626.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0626]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0626 : work0626.theta.ok = true ∧
    work0626.jac.invOK = true ∧ acceptsUnitSq work0626.out = true := by decide +kernel

def cell0626 : CellCertificate where
  tauBall := tau0626
  contactCenter := center0626
  contactBall := contact0626
  work := work0626
  center_sq := center_sq0626
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0626.1
  jac_ok := checks0626.2.1
  accepted := checks0626.2.2

def tau0627 : RatBall :=
  ⟨⟨31/160, -47/160⟩, 3/320⟩
def center0627 : GaussianRat :=
  ⟨5788509/40000000, -200941561/1000000000⟩
def contact0627 : RatBall := localContactBall tau0627 center0627
def work0627 : RoundedTauEval :=
  evalTau precision tau0627 contact0627 logTwoBall

theorem center_sq0627 : (center0627.re : ℝ)^2 +
    (center0627.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0627]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0627 : work0627.theta.ok = true ∧
    work0627.jac.invOK = true ∧ acceptsUnitSq work0627.out = true := by decide +kernel

def cell0627 : CellCertificate where
  tauBall := tau0627
  contactCenter := center0627
  contactBall := contact0627
  work := work0627
  center_sq := center_sq0627
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0627.1
  jac_ok := checks0627.2.1
  accepted := checks0627.2.2

def tau0628 : RatBall :=
  ⟨⟨29/160, -9/32⟩, 3/320⟩
def center0628 : GaussianRat :=
  ⟨67331309/500000000, -193009163/1000000000⟩
def contact0628 : RatBall := localContactBall tau0628 center0628
def work0628 : RoundedTauEval :=
  evalTau precision tau0628 contact0628 logTwoBall

theorem center_sq0628 : (center0628.re : ℝ)^2 +
    (center0628.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0628]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0628 : work0628.theta.ok = true ∧
    work0628.jac.invOK = true ∧ acceptsUnitSq work0628.out = true := by decide +kernel

def cell0628 : CellCertificate where
  tauBall := tau0628
  contactCenter := center0628
  contactBall := contact0628
  work := work0628
  center_sq := center_sq0628
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0628.1
  jac_ok := checks0628.2.1
  accepted := checks0628.2.2

def tau0629 : RatBall :=
  ⟨⟨31/160, -9/32⟩, 3/320⟩
def center0629 : GaussianRat :=
  ⟨143625227/1000000000, -38396169/200000000⟩
def contact0629 : RatBall := localContactBall tau0629 center0629
def work0629 : RoundedTauEval :=
  evalTau precision tau0629 contact0629 logTwoBall

theorem center_sq0629 : (center0629.re : ℝ)^2 +
    (center0629.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0629]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0629 : work0629.theta.ok = true ∧
    work0629.jac.invOK = true ∧ acceptsUnitSq work0629.out = true := by decide +kernel

def cell0629 : CellCertificate where
  tauBall := tau0629
  contactCenter := center0629
  contactBall := contact0629
  work := work0629
  center_sq := center_sq0629
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0629.1
  jac_ok := checks0629.2.1
  accepted := checks0629.2.2

def tau0630 : RatBall :=
  ⟨⟨5/32, -43/160⟩, 3/320⟩
def center0630 : GaussianRat :=
  ⟨57855523/500000000, -185818573/1000000000⟩
def contact0630 : RatBall := localContactBall tau0630 center0630
def work0630 : RoundedTauEval :=
  evalTau precision tau0630 contact0630 logTwoBall

theorem center_sq0630 : (center0630.re : ℝ)^2 +
    (center0630.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0630]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0630 : work0630.theta.ok = true ∧
    work0630.jac.invOK = true ∧ acceptsUnitSq work0630.out = true := by decide +kernel

def cell0630 : CellCertificate where
  tauBall := tau0630
  contactCenter := center0630
  contactBall := contact0630
  work := work0630
  center_sq := center_sq0630
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0630.1
  jac_ok := checks0630.2.1
  accepted := checks0630.2.2

def tau0631 : RatBall :=
  ⟨⟨27/160, -43/160⟩, 3/320⟩
def center0631 : GaussianRat :=
  ⟨1948873/15625000, -92480083/500000000⟩
def contact0631 : RatBall := localContactBall tau0631 center0631
def work0631 : RoundedTauEval :=
  evalTau precision tau0631 contact0631 logTwoBall

theorem center_sq0631 : (center0631.re : ℝ)^2 +
    (center0631.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0631]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0631 : work0631.theta.ok = true ∧
    work0631.jac.invOK = true ∧ acceptsUnitSq work0631.out = true := by decide +kernel

def cell0631 : CellCertificate where
  tauBall := tau0631
  contactCenter := center0631
  contactBall := contact0631
  work := work0631
  center_sq := center_sq0631
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0631.1
  jac_ok := checks0631.2.1
  accepted := checks0631.2.2

def cells : List CellCertificate := [cell0624, cell0625, cell0626, cell0627, cell0628, cell0629, cell0630, cell0631]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0078

end


