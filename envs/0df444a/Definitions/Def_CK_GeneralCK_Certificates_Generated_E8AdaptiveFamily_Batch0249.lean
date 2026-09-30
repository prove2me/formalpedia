-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0249
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0249
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:34:42.711959+00:00
-- url     : https://prove2.me/theorems/7cc27550-7331-4050-b25c-aec20a29f957
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0249.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0249_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact1998 : RatBall := localContactBall tau1998 center1998
def work1998 : RoundedTauEval :=
  evalTau precision tau1998 contact1998 logTwoBall

theorem center_sq1998 : (center1998.re : ℝ)^2 +
    (center1998.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1998]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1998 : work1998.theta.ok = true ∧
    work1998.jac.invOK = true ∧ acceptsUnitSq work1998.out = true := by decide +kernel

def cell1998 : CellCertificate where
  tauBall := tau1998
  contactCenter := center1998
  contactBall := contact1998
  work := work1998
  center_sq := center_sq1998
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1998.1
  jac_ok := checks1998.2.1
  accepted := checks1998.2.2

def tau1999 : RatBall :=
  ⟨⟨-15/64, 101/320⟩, 3/640⟩
def center1999 : GaussianRat :=
  ⟨-21994767/125000000, 212432751/1000000000⟩
def contact1999 : RatBall := localContactBall tau1999 center1999
def work1999 : RoundedTauEval :=
  evalTau precision tau1999 contact1999 logTwoBall

theorem center_sq1999 : (center1999.re : ℝ)^2 +
    (center1999.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1999]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1999 : work1999.theta.ok = true ∧
    work1999.jac.invOK = true ∧ acceptsUnitSq work1999.out = true := by decide +kernel

def cell1999 : CellCertificate where
  tauBall := tau1999
  contactCenter := center1999
  contactBall := contact1999
  work := work1999
  center_sq := center_sq1999
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1999.1
  jac_ok := checks1999.2.1
  accepted := checks1999.2.2

def cells : List CellCertificate := [cell1992, cell1993, cell1994, cell1995, cell1996, cell1997, cell1998, cell1999]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249


