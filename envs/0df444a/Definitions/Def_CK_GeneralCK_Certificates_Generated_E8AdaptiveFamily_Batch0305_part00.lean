-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0305_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0305_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:20:30.894285+00:00
-- url     : https://prove2.me/theorems/14daa534-f636-4905-8eb8-48a01f89fb26
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0305 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2440 : RatBall :=
  ⟨⟨73/320, 93/320⟩, 3/640⟩
def center2440 : GaussianRat :=
  ⟨84433841/500000000, 195452163/1000000000⟩
def contact2440 : RatBall := localContactBall tau2440 center2440
def work2440 : RoundedTauEval :=
  evalTau precision tau2440 contact2440 logTwoBall

theorem center_sq2440 : (center2440.re : ℝ)^2 +
    (center2440.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2440]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2440 : work2440.theta.ok = true ∧
    work2440.jac.invOK = true ∧ acceptsUnitSq work2440.out = true := by decide +kernel

def cell2440 : CellCertificate where
  tauBall := tau2440
  contactCenter := center2440
  contactBall := contact2440
  work := work2440
  center_sq := center_sq2440
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2440.1
  jac_ok := checks2440.2.1
  accepted := checks2440.2.2

def tau2441 : RatBall :=
  ⟨⟨15/64, 93/320⟩, 3/640⟩
def center2441 : GaussianRat :=
  ⟨173254189/1000000000, 38963859/200000000⟩
def contact2441 : RatBall := localContactBall tau2441 center2441
def work2441 : RoundedTauEval :=
  evalTau precision tau2441 contact2441 logTwoBall

theorem center_sq2441 : (center2441.re : ℝ)^2 +
    (center2441.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2441]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2441 : work2441.theta.ok = true ∧
    work2441.jac.invOK = true ∧ acceptsUnitSq work2441.out = true := by decide +kernel

def cell2441 : CellCertificate where
  tauBall := tau2441
  contactCenter := center2441
  contactBall := contact2441
  work := work2441
  center_sq := center_sq2441
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2441.1
  jac_ok := checks2441.2.1
  accepted := checks2441.2.2

def tau2442 : RatBall :=
  ⟨⟨73/320, 19/64⟩, 3/640⟩
def center2442 : GaussianRat :=
  ⟨16950309/100000000, 199854009/1000000000⟩
def contact2442 : RatBall := localContactBall tau2442 center2442
def work2442 : RoundedTauEval :=
  evalTau precision tau2442 contact2442 logTwoBall

theorem center_sq2442 : (center2442.re : ℝ)^2 +
    (center2442.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2442]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2442 : work2442.theta.ok = true ∧
    work2442.jac.invOK = true ∧ acceptsUnitSq work2442.out = true := by decide +kernel

def cell2442 : CellCertificate where
  tauBall := tau2442
  contactCenter := center2442
  contactBall := contact2442
  work := work2442
  center_sq := center_sq2442
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2442.1
  jac_ok := checks2442.2.1
  accepted := checks2442.2.2

def tau2443 : RatBall :=
  ⟨⟨15/64, 19/64⟩, 3/640⟩
def center2443 : GaussianRat :=
  ⟨43475599/250000000, 199203157/1000000000⟩
def contact2443 : RatBall := localContactBall tau2443 center2443
def work2443 : RoundedTauEval :=
  evalTau precision tau2443 contact2443 logTwoBall

theorem center_sq2443 : (center2443.re : ℝ)^2 +
    (center2443.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2443]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2443 : work2443.theta.ok = true ∧
    work2443.jac.invOK = true ∧ acceptsUnitSq work2443.out = true := by decide +kernel

def cell2443 : CellCertificate where
  tauBall := tau2443
  contactCenter := center2443
  contactBall := contact2443
  work := work2443
  center_sq := center_sq2443
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2443.1
  jac_ok := checks2443.2.1
  accepted := checks2443.2.2

def tau2444 : RatBall :=
  ⟨⟨77/320, 93/320⟩, 3/640⟩
def center2444 : GaussianRat :=
  ⟨44405679/250000000, 194173939/1000000000⟩
def contact2444 : RatBall := localContactBall tau2444 center2444
def work2444 : RoundedTauEval :=
  evalTau precision tau2444 contact2444 logTwoBall

theorem center_sq2444 : (center2444.re : ℝ)^2 +
    (center2444.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2444]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305


