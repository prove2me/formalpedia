-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0002_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0002_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:10:55.918298+00:00
-- url     : https://prove2.me/theorems/4558db6b-cd8a-45de-b681-97c0a88ce1f7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0002 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0016 : RatBall :=
  ⟨⟨1/8, -1/8⟩, 3/80⟩
def center0016 : GaussianRat :=
  ⟨87563403/1000000000, -85687457/1000000000⟩
def contact0016 : RatBall := localContactBall tau0016 center0016
def work0016 : RoundedTauEval :=
  evalTau precision tau0016 contact0016 logTwoBall

theorem center_sq0016 : (center0016.re : ℝ)^2 +
    (center0016.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0016]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0016 : work0016.theta.ok = true ∧
    work0016.jac.invOK = true ∧ acceptsUnitSq work0016.out = true := by decide +kernel

def cell0016 : CellCertificate where
  tauBall := tau0016
  contactCenter := center0016
  contactBall := contact0016
  work := work0016
  center_sq := center_sq0016
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0016.1
  jac_ok := checks0016.2.1
  accepted := checks0016.2.2

def tau0017 : RatBall :=
  ⟨⟨1/40, -3/40⟩, 3/80⟩
def center0017 : GaussianRat :=
  ⟨2178341/125000000, -3253349/62500000⟩
def contact0017 : RatBall := localContactBall tau0017 center0017
def work0017 : RoundedTauEval :=
  evalTau precision tau0017 contact0017 logTwoBall

theorem center_sq0017 : (center0017.re : ℝ)^2 +
    (center0017.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0017]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0017 : work0017.theta.ok = true ∧
    work0017.jac.invOK = true ∧ acceptsUnitSq work0017.out = true := by decide +kernel

def cell0017 : CellCertificate where
  tauBall := tau0017
  contactCenter := center0017
  contactBall := contact0017
  work := work0017
  center_sq := center_sq0017
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0017.1
  jac_ok := checks0017.2.1
  accepted := checks0017.2.2

def tau0018 : RatBall :=
  ⟨⟨3/40, -3/40⟩, 3/80⟩
def center0018 : GaussianRat :=
  ⟨1304683/25000000, -51781961/1000000000⟩
def contact0018 : RatBall := localContactBall tau0018 center0018
def work0018 : RoundedTauEval :=
  evalTau precision tau0018 contact0018 logTwoBall

theorem center_sq0018 : (center0018.re : ℝ)^2 +
    (center0018.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0018]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0018 : work0018.theta.ok = true ∧
    work0018.jac.invOK = true ∧ acceptsUnitSq work0018.out = true := by decide +kernel

def cell0018 : CellCertificate where
  tauBall := tau0018
  contactCenter := center0018
  contactBall := contact0018
  work := work0018
  center_sq := center_sq0018
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0018.1
  jac_ok := checks0018.2.1
  accepted := checks0018.2.2

def tau0019 : RatBall :=
  ⟨⟨1/40, -1/40⟩, 3/80⟩
def center0019 : GaussianRat :=
  ⟨17336181/1000000000, -17321167/1000000000⟩
def contact0019 : RatBall := localContactBall tau0019 center0019
def work0019 : RoundedTauEval :=
  evalTau precision tau0019 contact0019 logTwoBall

theorem center_sq0019 : (center0019.re : ℝ)^2 +
    (center0019.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0019]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0019 : work0019.theta.ok = true ∧
    work0019.jac.invOK = true ∧ acceptsUnitSq work0019.out = true := by decide +kernel

def cell0019 : CellCertificate where
  tauBall := tau0019
  contactCenter := center0019
  contactBall := contact0019
  work := work0019
  center_sq := center_sq0019
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0019.1
  jac_ok := checks0019.2.1
  accepted := checks0019.2.2

def tau0020 : RatBall :=
  ⟨⟨3/40, -1/40⟩, 3/80⟩
def center0020 : GaussianRat :=
  ⟨51918459/1000000000, -861577/50000000⟩
def contact0020 : RatBall := localContactBall tau0020 center0020
def work0020 : RoundedTauEval :=
  evalTau precision tau0020 contact0020 logTwoBall

theorem center_sq0020 : (center0020.re : ℝ)^2 +
    (center0020.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0020]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0020 : work0020.theta.ok = true ∧
    work0020.jac.invOK = true ∧ acceptsUnitSq work0020.out = true := by decide +kernel

def cell0020 : CellCertificate where
  tauBall := tau0020
  contactCenter := center0020
  contactBall := contact0020
  work := work0020
  center_sq := center_sq0020
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0020.1
  jac_ok := checks0020.2.1
  accepted := checks0020.2.2

def tau0021 : RatBall :=
  ⟨⟨1/8, -3/40⟩, 3/80⟩
def center0021 : GaussianRat :=
  ⟨86672281/1000000000, -1024941/20000000⟩
def contact0021 : RatBall := localContactBall tau0021 center0021
def work0021 : RoundedTauEval :=
  evalTau precision tau0021 contact0021 logTwoBall

theorem center_sq0021 : (center0021.re : ℝ)^2 +
    (center0021.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0021]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0021 : work0021.theta.ok = true ∧
    work0021.jac.invOK = true ∧ acceptsUnitSq work0021.out = true := by decide +kernel

def cell0021 : CellCertificate where
  tauBall := tau0021
  contactCenter := center0021
  contactBall := contact0021
  work := work0021
  center_sq := center_sq0021
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0021.1
  jac_ok := checks0021.2.1
  accepted := checks0021.2.2

def tau0022 : RatBall :=
  ⟨⟨7/40, -3/40⟩, 3/80⟩
def center0022 : GaussianRat :=
  ⟨7544217/62500000, -12616221/250000000⟩
def contact0022 : RatBall := localContactBall tau0022 center0022
def work0022 : RoundedTauEval :=
  evalTau precision tau0022 contact0022 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002


