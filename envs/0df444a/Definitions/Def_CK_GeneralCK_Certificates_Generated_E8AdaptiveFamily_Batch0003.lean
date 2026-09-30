-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0003
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0003
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:09:11.958656+00:00
-- url     : https://prove2.me/theorems/7c580263-ce48-42b8-98c5-9669f3d4d416
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0003` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0003` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0003` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0003 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0003.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0003_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0003

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0030 : work0030.theta.ok = true ∧
    work0030.jac.invOK = true ∧ acceptsUnitSq work0030.out = true := by decide +kernel

def cell0030 : CellCertificate where
  tauBall := tau0030
  contactCenter := center0030
  contactBall := contact0030
  work := work0030
  center_sq := center_sq0030
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0030.1
  jac_ok := checks0030.2.1
  accepted := checks0030.2.2

def tau0031 : RatBall :=
  ⟨⟨-3/40, 1/40⟩, 3/80⟩
def center0031 : GaussianRat :=
  ⟨-51918459/1000000000, 861577/50000000⟩
def contact0031 : RatBall := localContactBall tau0031 center0031
def work0031 : RoundedTauEval :=
  evalTau precision tau0031 contact0031 logTwoBall

theorem center_sq0031 : (center0031.re : ℝ)^2 +
    (center0031.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0031]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0031 : work0031.theta.ok = true ∧
    work0031.jac.invOK = true ∧ acceptsUnitSq work0031.out = true := by decide +kernel

def cell0031 : CellCertificate where
  tauBall := tau0031
  contactCenter := center0031
  contactBall := contact0031
  work := work0031
  center_sq := center_sq0031
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0031.1
  jac_ok := checks0031.2.1
  accepted := checks0031.2.2

def cells : List CellCertificate := [cell0024, cell0025, cell0026, cell0027, cell0028, cell0029, cell0030, cell0031]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0003


