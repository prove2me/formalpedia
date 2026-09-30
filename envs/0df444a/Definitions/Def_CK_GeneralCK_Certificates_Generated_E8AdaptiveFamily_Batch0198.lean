-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0198
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0198
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:47:34.793985+00:00
-- url     : https://prove2.me/theorems/8d73527b-09f7-483e-9965-780d38a1d2ba
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0198.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0198_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center1590 : GaussianRat :=
  ⟨14490933/250000000, -269422101/1000000000⟩
def contact1590 : RatBall := localContactBall tau1590 center1590
def work1590 : RoundedTauEval :=
  evalTau precision tau1590 contact1590 logTwoBall

theorem center_sq1590 : (center1590.re : ℝ)^2 +
    (center1590.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1590]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1590 : work1590.theta.ok = true ∧
    work1590.jac.invOK = true ∧ acceptsUnitSq work1590.out = true := by decide +kernel

def cell1590 : CellCertificate where
  tauBall := tau1590
  contactCenter := center1590
  contactBall := contact1590
  work := work1590
  center_sq := center_sq1590
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1590.1
  jac_ok := checks1590.2.1
  accepted := checks1590.2.2

def tau1591 : RatBall :=
  ⟨⟨21/320, -117/320⟩, 3/640⟩
def center1591 : GaussianRat :=
  ⟨52663303/1000000000, -52945801/200000000⟩
def contact1591 : RatBall := localContactBall tau1591 center1591
def work1591 : RoundedTauEval :=
  evalTau precision tau1591 contact1591 logTwoBall

theorem center_sq1591 : (center1591.re : ℝ)^2 +
    (center1591.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1591]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1591 : work1591.theta.ok = true ∧
    work1591.jac.invOK = true ∧ acceptsUnitSq work1591.out = true := by decide +kernel

def cell1591 : CellCertificate where
  tauBall := tau1591
  contactCenter := center1591
  contactBall := contact1591
  work := work1591
  center_sq := center_sq1591
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1591.1
  jac_ok := checks1591.2.1
  accepted := checks1591.2.2

def cells : List CellCertificate := [cell1584, cell1585, cell1586, cell1587, cell1588, cell1589, cell1590, cell1591]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198


