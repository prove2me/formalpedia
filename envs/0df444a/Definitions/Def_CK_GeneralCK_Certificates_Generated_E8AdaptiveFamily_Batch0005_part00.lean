-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0005_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0005_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:51:16.447237+00:00
-- url     : https://prove2.me/theorems/6f6b4fd2-3e1e-49f5-a10b-4c759cb57563
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0005 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0040 : RatBall :=
  ⟨⟨3/40, 1/40⟩, 3/80⟩
def center0040 : GaussianRat :=
  ⟨51918459/1000000000, 861577/50000000⟩
def contact0040 : RatBall := localContactBall tau0040 center0040
def work0040 : RoundedTauEval :=
  evalTau precision tau0040 contact0040 logTwoBall

theorem center_sq0040 : (center0040.re : ℝ)^2 +
    (center0040.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0040]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0040 : work0040.theta.ok = true ∧
    work0040.jac.invOK = true ∧ acceptsUnitSq work0040.out = true := by decide +kernel

def cell0040 : CellCertificate where
  tauBall := tau0040
  contactCenter := center0040
  contactBall := contact0040
  work := work0040
  center_sq := center_sq0040
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0040.1
  jac_ok := checks0040.2.1
  accepted := checks0040.2.2

def tau0041 : RatBall :=
  ⟨⟨1/40, 3/40⟩, 3/80⟩
def center0041 : GaussianRat :=
  ⟨2178341/125000000, 3253349/62500000⟩
def contact0041 : RatBall := localContactBall tau0041 center0041
def work0041 : RoundedTauEval :=
  evalTau precision tau0041 contact0041 logTwoBall

theorem center_sq0041 : (center0041.re : ℝ)^2 +
    (center0041.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0041]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0041 : work0041.theta.ok = true ∧
    work0041.jac.invOK = true ∧ acceptsUnitSq work0041.out = true := by decide +kernel

def cell0041 : CellCertificate where
  tauBall := tau0041
  contactCenter := center0041
  contactBall := contact0041
  work := work0041
  center_sq := center_sq0041
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0041.1
  jac_ok := checks0041.2.1
  accepted := checks0041.2.2

def tau0042 : RatBall :=
  ⟨⟨3/40, 3/40⟩, 3/80⟩
def center0042 : GaussianRat :=
  ⟨1304683/25000000, 51781961/1000000000⟩
def contact0042 : RatBall := localContactBall tau0042 center0042
def work0042 : RoundedTauEval :=
  evalTau precision tau0042 contact0042 logTwoBall

theorem center_sq0042 : (center0042.re : ℝ)^2 +
    (center0042.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0042]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0042 : work0042.theta.ok = true ∧
    work0042.jac.invOK = true ∧ acceptsUnitSq work0042.out = true := by decide +kernel

def cell0042 : CellCertificate where
  tauBall := tau0042
  contactCenter := center0042
  contactBall := contact0042
  work := work0042
  center_sq := center_sq0042
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0042.1
  jac_ok := checks0042.2.1
  accepted := checks0042.2.2

def tau0043 : RatBall :=
  ⟨⟨1/8, 1/40⟩, 3/80⟩
def center0043 : GaussianRat :=
  ⟨8623323/100000000, 17054997/1000000000⟩
def contact0043 : RatBall := localContactBall tau0043 center0043
def work0043 : RoundedTauEval :=
  evalTau precision tau0043 contact0043 logTwoBall

theorem center_sq0043 : (center0043.re : ℝ)^2 +
    (center0043.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0043]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0043 : work0043.theta.ok = true ∧
    work0043.jac.invOK = true ∧ acceptsUnitSq work0043.out = true := by decide +kernel

def cell0043 : CellCertificate where
  tauBall := tau0043
  contactCenter := center0043
  contactBall := contact0043
  work := work0043
  center_sq := center_sq0043
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0043.1
  jac_ok := checks0043.2.1
  accepted := checks0043.2.2

def tau0044 : RatBall :=
  ⟨⟨7/40, 1/40⟩, 3/80⟩
def center0044 : GaussianRat :=
  ⟨120111093/1000000000, 16796751/1000000000⟩
def contact0044 : RatBall := localContactBall tau0044 center0044
def work0044 : RoundedTauEval :=
  evalTau precision tau0044 contact0044 logTwoBall

theorem center_sq0044 : (center0044.re : ℝ)^2 +
    (center0044.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0044]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0044 : work0044.theta.ok = true ∧
    work0044.jac.invOK = true ∧ acceptsUnitSq work0044.out = true := by decide +kernel

def cell0044 : CellCertificate where
  tauBall := tau0044
  contactCenter := center0044
  contactBall := contact0044
  work := work0044
  center_sq := center_sq0044
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0044.1
  jac_ok := checks0044.2.1
  accepted := checks0044.2.2

def tau0045 : RatBall :=
  ⟨⟨1/8, 3/40⟩, 3/80⟩
def center0045 : GaussianRat :=
  ⟨86672281/1000000000, 1024941/20000000⟩
def contact0045 : RatBall := localContactBall tau0045 center0045
def work0045 : RoundedTauEval :=
  evalTau precision tau0045 contact0045 logTwoBall

theorem center_sq0045 : (center0045.re : ℝ)^2 +
    (center0045.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0045]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0045 : work0045.theta.ok = true ∧
    work0045.jac.invOK = true ∧ acceptsUnitSq work0045.out = true := by decide +kernel

def cell0045 : CellCertificate where
  tauBall := tau0045
  contactCenter := center0045
  contactBall := contact0045
  work := work0045
  center_sq := center_sq0045
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0045.1
  jac_ok := checks0045.2.1
  accepted := checks0045.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005


