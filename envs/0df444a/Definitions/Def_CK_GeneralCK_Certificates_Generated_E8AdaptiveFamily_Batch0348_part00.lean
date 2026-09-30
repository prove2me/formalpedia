-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0348_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0348_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:47:28.130896+00:00
-- url     : https://prove2.me/theorems/2a6f0505-8ecf-4cad-96aa-8c91f91e4d94
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0348 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0348 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0348 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0348 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0348 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0348

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2784 : RatBall :=
  ⟨⟨-7/128, -251/640⟩, 3/1280⟩
def center2784 : GaussianRat :=
  ⟨-45003787/1000000000, -57338531/200000000⟩
def contact2784 : RatBall := localContactBall tau2784 center2784
def work2784 : RoundedTauEval :=
  evalTau precision tau2784 contact2784 logTwoBall

theorem center_sq2784 : (center2784.re : ℝ)^2 +
    (center2784.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2784]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2784 : work2784.theta.ok = true ∧
    work2784.jac.invOK = true ∧ acceptsUnitSq work2784.out = true := by decide +kernel

def cell2784 : CellCertificate where
  tauBall := tau2784
  contactCenter := center2784
  contactBall := contact2784
  work := work2784
  center_sq := center_sq2784
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2784.1
  jac_ok := checks2784.2.1
  accepted := checks2784.2.2

def tau2785 : RatBall :=
  ⟨⟨-33/640, -251/640⟩, 3/1280⟩
def center2785 : GaussianRat :=
  ⟨-42442179/1000000000, -286823589/1000000000⟩
def contact2785 : RatBall := localContactBall tau2785 center2785
def work2785 : RoundedTauEval :=
  evalTau precision tau2785 contact2785 logTwoBall

theorem center_sq2785 : (center2785.re : ℝ)^2 +
    (center2785.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2785]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2785 : work2785.theta.ok = true ∧
    work2785.jac.invOK = true ∧ acceptsUnitSq work2785.out = true := by decide +kernel

def cell2785 : CellCertificate where
  tauBall := tau2785
  contactCenter := center2785
  contactBall := contact2785
  work := work2785
  center_sq := center_sq2785
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2785.1
  jac_ok := checks2785.2.1
  accepted := checks2785.2.2

def tau2786 : RatBall :=
  ⟨⟨-7/128, -249/640⟩, 3/1280⟩
def center2786 : GaussianRat :=
  ⟨-22435003/500000000, -284135717/1000000000⟩
def contact2786 : RatBall := localContactBall tau2786 center2786
def work2786 : RoundedTauEval :=
  evalTau precision tau2786 contact2786 logTwoBall

theorem center_sq2786 : (center2786.re : ℝ)^2 +
    (center2786.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2786]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2786 : work2786.theta.ok = true ∧
    work2786.jac.invOK = true ∧ acceptsUnitSq work2786.out = true := by decide +kernel

def cell2786 : CellCertificate where
  tauBall := tau2786
  contactCenter := center2786
  contactBall := contact2786
  work := work2786
  center_sq := center_sq2786
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2786.1
  jac_ok := checks2786.2.1
  accepted := checks2786.2.2

def tau2787 : RatBall :=
  ⟨⟨-33/640, -249/640⟩, 3/1280⟩
def center2787 : GaussianRat :=
  ⟨-42315903/1000000000, -284264849/1000000000⟩
def contact2787 : RatBall := localContactBall tau2787 center2787
def work2787 : RoundedTauEval :=
  evalTau precision tau2787 contact2787 logTwoBall

theorem center_sq2787 : (center2787.re : ℝ)^2 +
    (center2787.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2787]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2787 : work2787.theta.ok = true ∧
    work2787.jac.invOK = true ∧ acceptsUnitSq work2787.out = true := by decide +kernel

def cell2787 : CellCertificate where
  tauBall := tau2787
  contactCenter := center2787
  contactBall := contact2787
  work := work2787
  center_sq := center_sq2787
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2787.1
  jac_ok := checks2787.2.1
  accepted := checks2787.2.2

def tau2788 : RatBall :=
  ⟨⟨-47/640, -247/640⟩, 3/1280⟩
def center2788 : GaussianRat :=
  ⟨-59976659/1000000000, -70167217/250000000⟩
def contact2788 : RatBall := localContactBall tau2788 center2788
def work2788 : RoundedTauEval :=
  evalTau precision tau2788 contact2788 logTwoBall

theorem center_sq2788 : (center2788.re : ℝ)^2 +
    (center2788.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2788]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2788 : work2788.theta.ok = true ∧
    work2788.jac.invOK = true ∧ acceptsUnitSq work2788.out = true := by decide +kernel

def cell2788 : CellCertificate where
  tauBall := tau2788
  contactCenter := center2788
  contactBall := contact2788
  work := work2788
  center_sq := center_sq2788
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2788.1
  jac_ok := checks2788.2.1
  accepted := checks2788.2.2

def tau2789 : RatBall :=
  ⟨⟨-9/128, -247/640⟩, 3/1280⟩
def center2789 : GaussianRat :=
  ⟨-2872117/50000000, -14041993/50000000⟩
def contact2789 : RatBall := localContactBall tau2789 center2789
def work2789 : RoundedTauEval :=
  evalTau precision tau2789 contact2789 logTwoBall

theorem center_sq2789 : (center2789.re : ℝ)^2 +
    (center2789.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2789]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2789 : work2789.theta.ok = true ∧
    work2789.jac.invOK = true ∧ acceptsUnitSq work2789.out = true := by decide +kernel

def cell2789 : CellCertificate where
  tauBall := tau2789
  contactCenter := center2789
  contactBall := contact2789
  work := work2789
  center_sq := center_sq2789
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2789.1
  jac_ok := checks2789.2.1
  accepted := checks2789.2.2

def tau2790 : RatBall :=
  ⟨⟨-47/640, -49/128⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0348


