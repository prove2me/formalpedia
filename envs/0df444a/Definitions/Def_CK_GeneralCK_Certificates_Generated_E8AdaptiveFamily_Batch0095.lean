-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0095
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0095
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:29:44.506641+00:00
-- url     : https://prove2.me/theorems/357ed3e0-f102-42c6-b3eb-013701603440
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0095` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0095` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0095` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0095 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0095.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0095 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0095

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0760 : RatBall :=
  ⟨⟨61/160, -3/32⟩, 3/320⟩
def center0760 : GaussianRat :=
  ⟨50772973/200000000, -14125933/250000000⟩
def contact0760 : RatBall := localContactBall tau0760 center0760
def work0760 : RoundedTauEval :=
  evalTau precision tau0760 contact0760 logTwoBall

theorem center_sq0760 : (center0760.re : ℝ)^2 +
    (center0760.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0760]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0760 : work0760.theta.ok = true ∧
    work0760.jac.invOK = true ∧ acceptsUnitSq work0760.out = true := by decide +kernel

def cell0760 : CellCertificate where
  tauBall := tau0760
  contactCenter := center0760
  contactBall := contact0760
  work := work0760
  center_sq := center_sq0760
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0760.1
  jac_ok := checks0760.2.1
  accepted := checks0760.2.2

def tau0761 : RatBall :=
  ⟨⟨63/160, -3/32⟩, 3/320⟩
def center0761 : GaussianRat :=
  ⟨65346019/250000000, -28003013/500000000⟩
def contact0761 : RatBall := localContactBall tau0761 center0761
def work0761 : RoundedTauEval :=
  evalTau precision tau0761 contact0761 logTwoBall

theorem center_sq0761 : (center0761.re : ℝ)^2 +
    (center0761.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0761]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0761 : work0761.theta.ok = true ∧
    work0761.jac.invOK = true ∧ acceptsUnitSq work0761.out = true := by decide +kernel

def cell0761 : CellCertificate where
  tauBall := tau0761
  contactCenter := center0761
  contactBall := contact0761
  work := work0761
  center_sq := center_sq0761
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0761.1
  jac_ok := checks0761.2.1
  accepted := checks0761.2.2

def tau0762 : RatBall :=
  ⟨⟨61/160, -13/160⟩, 3/320⟩
def center0762 : GaussianRat :=
  ⟨126702243/500000000, -6119291/125000000⟩
def contact0762 : RatBall := localContactBall tau0762 center0762
def work0762 : RoundedTauEval :=
  evalTau precision tau0762 contact0762 logTwoBall

theorem center_sq0762 : (center0762.re : ℝ)^2 +
    (center0762.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0762]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0762 : work0762.theta.ok = true ∧
    work0762.jac.invOK = true ∧ acceptsUnitSq work0762.out = true := by decide +kernel

def cell0762 : CellCertificate where
  tauBall := tau0762
  contactCenter := center0762
  contactBall := contact0762
  work := work0762
  center_sq := center_sq0762
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0762.1
  jac_ok := checks0762.2.1
  accepted := checks0762.2.2

def tau0763 : RatBall :=
  ⟨⟨63/160, -13/160⟩, 3/320⟩
def center0763 : GaussianRat :=
  ⟨260916819/1000000000, -48524207/1000000000⟩
def contact0763 : RatBall := localContactBall tau0763 center0763
def work0763 : RoundedTauEval :=
  evalTau precision tau0763 contact0763 logTwoBall

theorem center_sq0763 : (center0763.re : ℝ)^2 +
    (center0763.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0763]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0763 : work0763.theta.ok = true ∧
    work0763.jac.invOK = true ∧ acceptsUnitSq work0763.out = true := by decide +kernel

def cell0763 : CellCertificate where
  tauBall := tau0763
  contactCenter := center0763
  contactBall := contact0763
  work := work0763
  center_sq := center_sq0763
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0763.1
  jac_ok := checks0763.2.1
  accepted := checks0763.2.2

def tau0764 : RatBall :=
  ⟨⟨61/160, -11/160⟩, 3/320⟩
def center0764 : GaussianRat :=
  ⟨25301093/100000000, -41411583/1000000000⟩
def contact0764 : RatBall := localContactBall tau0764 center0764
def work0764 : RoundedTauEval :=
  evalTau precision tau0764 contact0764 logTwoBall

theorem center_sq0764 : (center0764.re : ℝ)^2 +
    (center0764.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0764]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0764 : work0764.theta.ok = true ∧
    work0764.jac.invOK = true ∧ acceptsUnitSq work0764.out = true := by decide +kernel

def cell0764 : CellCertificate where
  tauBall := tau0764
  contactCenter := center0764
  contactBall := contact0764
  work := work0764
  center_sq := center_sq0764
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0764.1
  jac_ok := checks0764.2.1
  accepted := checks0764.2.2

def tau0765 : RatBall :=
  ⟨⟨63/160, -11/160⟩, 3/320⟩
def center0765 : GaussianRat :=
  ⟨260517353/1000000000, -1026213/25000000⟩
def contact0765 : RatBall := localContactBall tau0765 center0765
def work0765 : RoundedTauEval :=
  evalTau precision tau0765 contact0765 logTwoBall

theorem center_sq0765 : (center0765.re : ℝ)^2 +
    (center0765.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0765]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0765 : work0765.theta.ok = true ∧
    work0765.jac.invOK = true ∧ acceptsUnitSq work0765.out = true := by decide +kernel

def cell0765 : CellCertificate where
  tauBall := tau0765
  contactCenter := center0765
  contactBall := contact0765
  work := work0765
  center_sq := center_sq0765
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0765.1
  jac_ok := checks0765.2.1
  accepted := checks0765.2.2

def tau0766 : RatBall :=
  ⟨⟨61/160, -9/160⟩, 3/320⟩
def center0766 : GaussianRat :=
  ⟨252683709/1000000000, -6774897/200000000⟩
def contact0766 : RatBall := localContactBall tau0766 center0766
def work0766 : RoundedTauEval :=
  evalTau precision tau0766 contact0766 logTwoBall

theorem center_sq0766 : (center0766.re : ℝ)^2 +
    (center0766.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0766]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0766 : work0766.theta.ok = true ∧
    work0766.jac.invOK = true ∧ acceptsUnitSq work0766.out = true := by decide +kernel

def cell0766 : CellCertificate where
  tauBall := tau0766
  contactCenter := center0766
  contactBall := contact0766
  work := work0766
  center_sq := center_sq0766
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0766.1
  jac_ok := checks0766.2.1
  accepted := checks0766.2.2

def tau0767 : RatBall :=
  ⟨⟨63/160, -9/160⟩, 3/320⟩
def center0767 : GaussianRat :=
  ⟨65046299/250000000, -6715607/200000000⟩
def contact0767 : RatBall := localContactBall tau0767 center0767
def work0767 : RoundedTauEval :=
  evalTau precision tau0767 contact0767 logTwoBall

theorem center_sq0767 : (center0767.re : ℝ)^2 +
    (center0767.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0767]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0767 : work0767.theta.ok = true ∧
    work0767.jac.invOK = true ∧ acceptsUnitSq work0767.out = true := by decide +kernel

def cell0767 : CellCertificate where
  tauBall := tau0767
  contactCenter := center0767
  contactBall := contact0767
  work := work0767
  center_sq := center_sq0767
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0767.1
  jac_ok := checks0767.2.1
  accepted := checks0767.2.2

def cells : List CellCertificate := [cell0760, cell0761, cell0762, cell0763, cell0764, cell0765, cell0766, cell0767]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0095

end


