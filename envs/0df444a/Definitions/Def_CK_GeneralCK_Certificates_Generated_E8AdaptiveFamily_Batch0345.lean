-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0345
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0345
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:57:22.911527+00:00
-- url     : https://prove2.me/theorems/215ca409-0cac-429e-958e-fce82c9ec96b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0345.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0345_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2764 : (center2764.re : ℝ)^2 +
    (center2764.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2764]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2764 : work2764.theta.ok = true ∧
    work2764.jac.invOK = true ∧ acceptsUnitSq work2764.out = true := by decide +kernel

def cell2764 : CellCertificate where
  tauBall := tau2764
  contactCenter := center2764
  contactBall := contact2764
  work := work2764
  center_sq := center_sq2764
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2764.1
  jac_ok := checks2764.2.1
  accepted := checks2764.2.2

def tau2765 : RatBall :=
  ⟨⟨-9/128, -253/640⟩, 3/1280⟩
def center2765 : GaussianRat :=
  ⟨-5795507/100000000, -288479173/1000000000⟩
def contact2765 : RatBall := localContactBall tau2765 center2765
def work2765 : RoundedTauEval :=
  evalTau precision tau2765 contact2765 logTwoBall

theorem center_sq2765 : (center2765.re : ℝ)^2 +
    (center2765.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2765]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2765 : work2765.theta.ok = true ∧
    work2765.jac.invOK = true ∧ acceptsUnitSq work2765.out = true := by decide +kernel

def cell2765 : CellCertificate where
  tauBall := tau2765
  contactCenter := center2765
  contactBall := contact2765
  work := work2765
  center_sq := center_sq2765
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2765.1
  jac_ok := checks2765.2.1
  accepted := checks2765.2.2

def tau2766 : RatBall :=
  ⟨⟨-43/640, -253/640⟩, 3/1280⟩
def center2766 : GaussianRat :=
  ⟨-55396349/1000000000, -28864989/100000000⟩
def contact2766 : RatBall := localContactBall tau2766 center2766
def work2766 : RoundedTauEval :=
  evalTau precision tau2766 contact2766 logTwoBall

theorem center_sq2766 : (center2766.re : ℝ)^2 +
    (center2766.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2766]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2766 : work2766.theta.ok = true ∧
    work2766.jac.invOK = true ∧ acceptsUnitSq work2766.out = true := by decide +kernel

def cell2766 : CellCertificate where
  tauBall := tau2766
  contactCenter := center2766
  contactBall := contact2766
  work := work2766
  center_sq := center_sq2766
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2766.1
  jac_ok := checks2766.2.1
  accepted := checks2766.2.2

def tau2767 : RatBall :=
  ⟨⟨-41/640, -253/640⟩, 3/1280⟩
def center2767 : GaussianRat :=
  ⟨-52835321/1000000000, -11552523/40000000⟩
def contact2767 : RatBall := localContactBall tau2767 center2767
def work2767 : RoundedTauEval :=
  evalTau precision tau2767 contact2767 logTwoBall

theorem center_sq2767 : (center2767.re : ℝ)^2 +
    (center2767.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2767]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2767 : work2767.theta.ok = true ∧
    work2767.jac.invOK = true ∧ acceptsUnitSq work2767.out = true := by decide +kernel

def cell2767 : CellCertificate where
  tauBall := tau2767
  contactCenter := center2767
  contactBall := contact2767
  work := work2767
  center_sq := center_sq2767
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2767.1
  jac_ok := checks2767.2.1
  accepted := checks2767.2.2

def cells : List CellCertificate := [cell2760, cell2761, cell2762, cell2763, cell2764, cell2765, cell2766, cell2767]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345


