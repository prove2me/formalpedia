-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0226
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0226
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:32:25.227904+00:00
-- url     : https://prove2.me/theorems/6d934d7f-2aeb-4d21-82b9-9f3ec75eb6d5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0226` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0226` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0226` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0226 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0226.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0226 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0226

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1808 : RatBall :=
  ⟨⟨83/320, -93/320⟩, 3/640⟩
def center1808 : GaussianRat :=
  ⟨95308733/500000000, -192166077/1000000000⟩
def contact1808 : RatBall := localContactBall tau1808 center1808
def work1808 : RoundedTauEval :=
  evalTau precision tau1808 contact1808 logTwoBall

theorem center_sq1808 : (center1808.re : ℝ)^2 +
    (center1808.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1808]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1808 : work1808.theta.ok = true ∧
    work1808.jac.invOK = true ∧ acceptsUnitSq work1808.out = true := by decide +kernel

def cell1808 : CellCertificate where
  tauBall := tau1808
  contactCenter := center1808
  contactBall := contact1808
  work := work1808
  center_sq := center_sq1808
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1808.1
  jac_ok := checks1808.2.1
  accepted := checks1808.2.2

def tau1809 : RatBall :=
  ⟨⟨17/64, -19/64⟩, 3/640⟩
def center1809 : GaussianRat :=
  ⟨39123719/200000000, -48940869/250000000⟩
def contact1809 : RatBall := localContactBall tau1809 center1809
def work1809 : RoundedTauEval :=
  evalTau precision tau1809 contact1809 logTwoBall

theorem center_sq1809 : (center1809.re : ℝ)^2 +
    (center1809.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1809]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1809 : work1809.theta.ok = true ∧
    work1809.jac.invOK = true ∧ acceptsUnitSq work1809.out = true := by decide +kernel

def cell1809 : CellCertificate where
  tauBall := tau1809
  contactCenter := center1809
  contactBall := contact1809
  work := work1809
  center_sq := center_sq1809
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1809.1
  jac_ok := checks1809.2.1
  accepted := checks1809.2.2

def tau1810 : RatBall :=
  ⟨⟨87/320, -19/64⟩, 3/640⟩
def center1810 : GaussianRat :=
  ⟨199903813/1000000000, -195040739/1000000000⟩
def contact1810 : RatBall := localContactBall tau1810 center1810
def work1810 : RoundedTauEval :=
  evalTau precision tau1810 contact1810 logTwoBall

theorem center_sq1810 : (center1810.re : ℝ)^2 +
    (center1810.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1810]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1810 : work1810.theta.ok = true ∧
    work1810.jac.invOK = true ∧ acceptsUnitSq work1810.out = true := by decide +kernel

def cell1810 : CellCertificate where
  tauBall := tau1810
  contactCenter := center1810
  contactBall := contact1810
  work := work1810
  center_sq := center_sq1810
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1810.1
  jac_ok := checks1810.2.1
  accepted := checks1810.2.2

def tau1811 : RatBall :=
  ⟨⟨17/64, -93/320⟩, 3/640⟩
def center1811 : GaussianRat :=
  ⟨97455589/500000000, -191473909/1000000000⟩
def contact1811 : RatBall := localContactBall tau1811 center1811
def work1811 : RoundedTauEval :=
  evalTau precision tau1811 contact1811 logTwoBall

theorem center_sq1811 : (center1811.re : ℝ)^2 +
    (center1811.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1811]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1811 : work1811.theta.ok = true ∧
    work1811.jac.invOK = true ∧ acceptsUnitSq work1811.out = true := by decide +kernel

def cell1811 : CellCertificate where
  tauBall := tau1811
  contactCenter := center1811
  contactBall := contact1811
  work := work1811
  center_sq := center_sq1811
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1811.1
  jac_ok := checks1811.2.1
  accepted := checks1811.2.2

def tau1812 : RatBall :=
  ⟨⟨87/320, -93/320⟩, 3/640⟩
def center1812 : GaussianRat :=
  ⟨2489819/12500000, -47692707/250000000⟩
def contact1812 : RatBall := localContactBall tau1812 center1812
def work1812 : RoundedTauEval :=
  evalTau precision tau1812 contact1812 logTwoBall

theorem center_sq1812 : (center1812.re : ℝ)^2 +
    (center1812.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1812]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1812 : work1812.theta.ok = true ∧
    work1812.jac.invOK = true ∧ acceptsUnitSq work1812.out = true := by decide +kernel

def cell1812 : CellCertificate where
  tauBall := tau1812
  contactCenter := center1812
  contactBall := contact1812
  work := work1812
  center_sq := center_sq1812
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1812.1
  jac_ok := checks1812.2.1
  accepted := checks1812.2.2

def tau1813 : RatBall :=
  ⟨⟨81/320, -91/320⟩, 3/640⟩
def center1813 : GaussianRat :=
  ⟨23204849/125000000, -94265223/500000000⟩
def contact1813 : RatBall := localContactBall tau1813 center1813
def work1813 : RoundedTauEval :=
  evalTau precision tau1813 contact1813 logTwoBall

theorem center_sq1813 : (center1813.re : ℝ)^2 +
    (center1813.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1813]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1813 : work1813.theta.ok = true ∧
    work1813.jac.invOK = true ∧ acceptsUnitSq work1813.out = true := by decide +kernel

def cell1813 : CellCertificate where
  tauBall := tau1813
  contactCenter := center1813
  contactBall := contact1813
  work := work1813
  center_sq := center_sq1813
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1813.1
  jac_ok := checks1813.2.1
  accepted := checks1813.2.2

def tau1814 : RatBall :=
  ⟨⟨83/320, -91/320⟩, 3/640⟩
def center1814 : GaussianRat :=
  ⟨37988073/200000000, -37573667/200000000⟩
def contact1814 : RatBall := localContactBall tau1814 center1814
def work1814 : RoundedTauEval :=
  evalTau precision tau1814 contact1814 logTwoBall

theorem center_sq1814 : (center1814.re : ℝ)^2 +
    (center1814.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1814]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1814 : work1814.theta.ok = true ∧
    work1814.jac.invOK = true ∧ acceptsUnitSq work1814.out = true := by decide +kernel

def cell1814 : CellCertificate where
  tauBall := tau1814
  contactCenter := center1814
  contactBall := contact1814
  work := work1814
  center_sq := center_sq1814
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1814.1
  jac_ok := checks1814.2.1
  accepted := checks1814.2.2

def tau1815 : RatBall :=
  ⟨⟨81/320, -89/320⟩, 3/640⟩
def center1815 : GaussianRat :=
  ⟨92495743/500000000, -184225151/1000000000⟩
def contact1815 : RatBall := localContactBall tau1815 center1815
def work1815 : RoundedTauEval :=
  evalTau precision tau1815 contact1815 logTwoBall

theorem center_sq1815 : (center1815.re : ℝ)^2 +
    (center1815.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1815]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1815 : work1815.theta.ok = true ∧
    work1815.jac.invOK = true ∧ acceptsUnitSq work1815.out = true := by decide +kernel

def cell1815 : CellCertificate where
  tauBall := tau1815
  contactCenter := center1815
  contactBall := contact1815
  work := work1815
  center_sq := center_sq1815
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1815.1
  jac_ok := checks1815.2.1
  accepted := checks1815.2.2

def cells : List CellCertificate := [cell1808, cell1809, cell1810, cell1811, cell1812, cell1813, cell1814, cell1815]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0226

end


