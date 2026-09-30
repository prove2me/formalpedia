-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0470
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0470
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:06:10.61347+00:00
-- url     : https://prove2.me/theorems/073d2cf6-5734-4776-beff-c983e3383672
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0470` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0470` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0470` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0470 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0470.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0470 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0470

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3760 : RatBall :=
  ⟨⟨71/640, 49/128⟩, 3/1280⟩
def center3760 : GaussianRat :=
  ⟨44958767/500000000, 275574013/1000000000⟩
def contact3760 : RatBall := localContactBall tau3760 center3760
def work3760 : RoundedTauEval :=
  evalTau precision tau3760 contact3760 logTwoBall

theorem center_sq3760 : (center3760.re : ℝ)^2 +
    (center3760.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3760]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3760 : work3760.theta.ok = true ∧
    work3760.jac.invOK = true ∧ acceptsUnitSq work3760.out = true := by decide +kernel

def cell3760 : CellCertificate where
  tauBall := tau3760
  contactCenter := center3760
  contactBall := contact3760
  work := work3760
  center_sq := center_sq3760
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3760.1
  jac_ok := checks3760.2.1
  accepted := checks3760.2.2

def tau3761 : RatBall :=
  ⟨⟨69/640, 247/640⟩, 3/1280⟩
def center3761 : GaussianRat :=
  ⟨87674459/1000000000, 278322741/1000000000⟩
def contact3761 : RatBall := localContactBall tau3761 center3761
def work3761 : RoundedTauEval :=
  evalTau precision tau3761 contact3761 logTwoBall

theorem center_sq3761 : (center3761.re : ℝ)^2 +
    (center3761.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3761]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3761 : work3761.theta.ok = true ∧
    work3761.jac.invOK = true ∧ acceptsUnitSq work3761.out = true := by decide +kernel

def cell3761 : CellCertificate where
  tauBall := tau3761
  contactCenter := center3761
  contactBall := contact3761
  work := work3761
  center_sq := center_sq3761
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3761.1
  jac_ok := checks3761.2.1
  accepted := checks3761.2.2

def tau3762 : RatBall :=
  ⟨⟨71/640, 247/640⟩, 3/1280⟩
def center3762 : GaussianRat :=
  ⟨90173701/1000000000, 278068181/1000000000⟩
def contact3762 : RatBall := localContactBall tau3762 center3762
def work3762 : RoundedTauEval :=
  evalTau precision tau3762 contact3762 logTwoBall

theorem center_sq3762 : (center3762.re : ℝ)^2 +
    (center3762.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3762]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3762 : work3762.theta.ok = true ∧
    work3762.jac.invOK = true ∧ acceptsUnitSq work3762.out = true := by decide +kernel

def cell3762 : CellCertificate where
  tauBall := tau3762
  contactCenter := center3762
  contactBall := contact3762
  work := work3762
  center_sq := center_sq3762
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3762.1
  jac_ok := checks3762.2.1
  accepted := checks3762.2.2

def tau3763 : RatBall :=
  ⟨⟨73/640, 241/640⟩, 3/1280⟩
def center3763 : GaussianRat :=
  ⟨11486457/125000000, 270354617/1000000000⟩
def contact3763 : RatBall := localContactBall tau3763 center3763
def work3763 : RoundedTauEval :=
  evalTau precision tau3763 contact3763 logTwoBall

theorem center_sq3763 : (center3763.re : ℝ)^2 +
    (center3763.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3763]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3763 : work3763.theta.ok = true ∧
    work3763.jac.invOK = true ∧ acceptsUnitSq work3763.out = true := by decide +kernel

def cell3763 : CellCertificate where
  tauBall := tau3763
  contactCenter := center3763
  contactBall := contact3763
  work := work3763
  center_sq := center_sq3763
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3763.1
  jac_ok := checks3763.2.1
  accepted := checks3763.2.2

def tau3764 : RatBall :=
  ⟨⟨15/128, 241/640⟩, 3/1280⟩
def center3764 : GaussianRat :=
  ⟨943643/10000000, 270097427/1000000000⟩
def contact3764 : RatBall := localContactBall tau3764 center3764
def work3764 : RoundedTauEval :=
  evalTau precision tau3764 contact3764 logTwoBall

theorem center_sq3764 : (center3764.re : ℝ)^2 +
    (center3764.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3764]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3764 : work3764.theta.ok = true ∧
    work3764.jac.invOK = true ∧ acceptsUnitSq work3764.out = true := by decide +kernel

def cell3764 : CellCertificate where
  tauBall := tau3764
  contactCenter := center3764
  contactBall := contact3764
  work := work3764
  center_sq := center_sq3764
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3764.1
  jac_ok := checks3764.2.1
  accepted := checks3764.2.2

def tau3765 : RatBall :=
  ⟨⟨73/640, 243/640⟩, 3/1280⟩
def center3765 : GaussianRat :=
  ⟨46073697/500000000, 54566443/200000000⟩
def contact3765 : RatBall := localContactBall tau3765 center3765
def work3765 : RoundedTauEval :=
  evalTau precision tau3765 contact3765 logTwoBall

theorem center_sq3765 : (center3765.re : ℝ)^2 +
    (center3765.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3765]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3765 : work3765.theta.ok = true ∧
    work3765.jac.invOK = true ∧ acceptsUnitSq work3765.out = true := by decide +kernel

def cell3765 : CellCertificate where
  tauBall := tau3765
  contactCenter := center3765
  contactBall := contact3765
  work := work3765
  center_sq := center_sq3765
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3765.1
  jac_ok := checks3765.2.1
  accepted := checks3765.2.2

def tau3766 : RatBall :=
  ⟨⟨15/128, 243/640⟩, 3/1280⟩
def center3766 : GaussianRat :=
  ⟨94626451/1000000000, 272571501/1000000000⟩
def contact3766 : RatBall := localContactBall tau3766 center3766
def work3766 : RoundedTauEval :=
  evalTau precision tau3766 contact3766 logTwoBall

theorem center_sq3766 : (center3766.re : ℝ)^2 +
    (center3766.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3766]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3766 : work3766.theta.ok = true ∧
    work3766.jac.invOK = true ∧ acceptsUnitSq work3766.out = true := by decide +kernel

def cell3766 : CellCertificate where
  tauBall := tau3766
  contactCenter := center3766
  contactBall := contact3766
  work := work3766
  center_sq := center_sq3766
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3766.1
  jac_ok := checks3766.2.1
  accepted := checks3766.2.2

def tau3767 : RatBall :=
  ⟨⟨77/640, 241/640⟩, 3/1280⟩
def center3767 : GaussianRat :=
  ⟨96833401/1000000000, 8432309/31250000⟩
def contact3767 : RatBall := localContactBall tau3767 center3767
def work3767 : RoundedTauEval :=
  evalTau precision tau3767 contact3767 logTwoBall

theorem center_sq3767 : (center3767.re : ℝ)^2 +
    (center3767.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3767]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3767 : work3767.theta.ok = true ∧
    work3767.jac.invOK = true ∧ acceptsUnitSq work3767.out = true := by decide +kernel

def cell3767 : CellCertificate where
  tauBall := tau3767
  contactCenter := center3767
  contactBall := contact3767
  work := work3767
  center_sq := center_sq3767
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3767.1
  jac_ok := checks3767.2.1
  accepted := checks3767.2.2

def cells : List CellCertificate := [cell3760, cell3761, cell3762, cell3763, cell3764, cell3765, cell3766, cell3767]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0470

end


