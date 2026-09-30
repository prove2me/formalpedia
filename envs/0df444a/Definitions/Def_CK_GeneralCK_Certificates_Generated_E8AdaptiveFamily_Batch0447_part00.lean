-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0447_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0447_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:06:08.927407+00:00
-- url     : https://prove2.me/theorems/59a19896-4e71-4e9d-9b32-969641784de0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447 (part 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447 (part 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447 (part 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447 (part 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0447 (part 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3576 : RatBall :=
  ⟨⟨17/640, 253/640⟩, 3/1280⟩
def center3576 : GaussianRat :=
  ⟨21961069/1000000000, 145086923/500000000⟩
def contact3576 : RatBall := localContactBall tau3576 center3576
def work3576 : RoundedTauEval :=
  evalTau precision tau3576 contact3576 logTwoBall

theorem center_sq3576 : (center3576.re : ℝ)^2 +
    (center3576.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3576]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3576 : work3576.theta.ok = true ∧
    work3576.jac.invOK = true ∧ acceptsUnitSq work3576.out = true := by decide +kernel

def cell3576 : CellCertificate where
  tauBall := tau3576
  contactCenter := center3576
  contactBall := contact3576
  work := work3576
  center_sq := center_sq3576
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3576.1
  jac_ok := checks3576.2.1
  accepted := checks3576.2.2

def tau3577 : RatBall :=
  ⟨⟨19/640, 253/640⟩, 3/1280⟩
def center3577 : GaussianRat :=
  ⟨24541601/1000000000, 290103079/1000000000⟩
def contact3577 : RatBall := localContactBall tau3577 center3577
def work3577 : RoundedTauEval :=
  evalTau precision tau3577 contact3577 logTwoBall

theorem center_sq3577 : (center3577.re : ℝ)^2 +
    (center3577.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3577]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3577 : work3577.theta.ok = true ∧
    work3577.jac.invOK = true ∧ acceptsUnitSq work3577.out = true := by decide +kernel

def cell3577 : CellCertificate where
  tauBall := tau3577
  contactCenter := center3577
  contactBall := contact3577
  work := work3577
  center_sq := center_sq3577
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3577.1
  jac_ok := checks3577.2.1
  accepted := checks3577.2.2

def tau3578 : RatBall :=
  ⟨⟨17/640, 51/128⟩, 3/1280⟩
def center3578 : GaussianRat :=
  ⟨22028391/1000000000, 146379397/500000000⟩
def contact3578 : RatBall := localContactBall tau3578 center3578
def work3578 : RoundedTauEval :=
  evalTau precision tau3578 contact3578 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447


