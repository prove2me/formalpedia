-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0361_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0361_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:04:12.234053+00:00
-- url     : https://prove2.me/theorems/de4025d4-a94e-4e25-9e9d-90c9ac040cd8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0361 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2888 : RatBall :=
  ⟨⟨1/128, -51/128⟩, 3/1280⟩
def center2888 : GaussianRat :=
  ⟨6481999/1000000000, -146511137/500000000⟩
def contact2888 : RatBall := localContactBall tau2888 center2888
def work2888 : RoundedTauEval :=
  evalTau precision tau2888 contact2888 logTwoBall

theorem center_sq2888 : (center2888.re : ℝ)^2 +
    (center2888.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2888]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2888 : work2888.theta.ok = true ∧
    work2888.jac.invOK = true ∧ acceptsUnitSq work2888.out = true := by decide +kernel

def cell2888 : CellCertificate where
  tauBall := tau2888
  contactCenter := center2888
  contactBall := contact2888
  work := work2888
  center_sq := center_sq2888
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2888.1
  jac_ok := checks2888.2.1
  accepted := checks2888.2.2

def tau2889 : RatBall :=
  ⟨⟨7/640, -51/128⟩, 3/1280⟩
def center2889 : GaussianRat :=
  ⟨9074409/1000000000, -292998297/1000000000⟩
def contact2889 : RatBall := localContactBall tau2889 center2889
def work2889 : RoundedTauEval :=
  evalTau precision tau2889 contact2889 logTwoBall

theorem center_sq2889 : (center2889.re : ℝ)^2 +
    (center2889.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2889]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2889 : work2889.theta.ok = true ∧
    work2889.jac.invOK = true ∧ acceptsUnitSq work2889.out = true := by decide +kernel

def cell2889 : CellCertificate where
  tauBall := tau2889
  contactCenter := center2889
  contactBall := contact2889
  work := work2889
  center_sq := center_sq2889
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2889.1
  jac_ok := checks2889.2.1
  accepted := checks2889.2.2

def tau2890 : RatBall :=
  ⟨⟨1/128, -253/640⟩, 3/1280⟩
def center2890 : GaussianRat :=
  ⟨1292431/200000000, -290433683/1000000000⟩
def contact2890 : RatBall := localContactBall tau2890 center2890
def work2890 : RoundedTauEval :=
  evalTau precision tau2890 contact2890 logTwoBall

theorem center_sq2890 : (center2890.re : ℝ)^2 +
    (center2890.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2890]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2890 : work2890.theta.ok = true ∧
    work2890.jac.invOK = true ∧ acceptsUnitSq work2890.out = true := by decide +kernel

def cell2890 : CellCertificate where
  tauBall := tau2890
  contactCenter := center2890
  contactBall := contact2890
  work := work2890
  center_sq := center_sq2890
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2890.1
  jac_ok := checks2890.2.1
  accepted := checks2890.2.2

def tau2891 : RatBall :=
  ⟨⟨7/640, -253/640⟩, 3/1280⟩
def center2891 : GaussianRat :=
  ⟨9046633/1000000000, -145205019/500000000⟩
def contact2891 : RatBall := localContactBall tau2891 center2891
def work2891 : RoundedTauEval :=
  evalTau precision tau2891 contact2891 logTwoBall

theorem center_sq2891 : (center2891.re : ℝ)^2 +
    (center2891.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2891]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2891 : work2891.theta.ok = true ∧
    work2891.jac.invOK = true ∧ acceptsUnitSq work2891.out = true := by decide +kernel

def cell2891 : CellCertificate where
  tauBall := tau2891
  contactCenter := center2891
  contactBall := contact2891
  work := work2891
  center_sq := center_sq2891
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2891.1
  jac_ok := checks2891.2.1
  accepted := checks2891.2.2

def tau2892 : RatBall :=
  ⟨⟨1/640, -251/640⟩, 3/1280⟩
def center2892 : GaussianRat :=
  ⟨1288571/1000000000, -287876293/1000000000⟩
def contact2892 : RatBall := localContactBall tau2892 center2892
def work2892 : RoundedTauEval :=
  evalTau precision tau2892 contact2892 logTwoBall

theorem center_sq2892 : (center2892.re : ℝ)^2 +
    (center2892.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2892]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2892 : work2892.theta.ok = true ∧
    work2892.jac.invOK = true ∧ acceptsUnitSq work2892.out = true := by decide +kernel

def cell2892 : CellCertificate where
  tauBall := tau2892
  contactCenter := center2892
  contactBall := contact2892
  work := work2892
  center_sq := center_sq2892
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2892.1
  jac_ok := checks2892.2.1
  accepted := checks2892.2.2

def tau2893 : RatBall :=
  ⟨⟨3/640, -251/640⟩, 3/1280⟩
def center2893 : GaussianRat :=
  ⟨193283/50000000, -143934259/500000000⟩
def contact2893 : RatBall := localContactBall tau2893 center2893
def work2893 : RoundedTauEval :=
  evalTau precision tau2893 contact2893 logTwoBall

theorem center_sq2893 : (center2893.re : ℝ)^2 +
    (center2893.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2893]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2893 : work2893.theta.ok = true ∧
    work2893.jac.invOK = true ∧ acceptsUnitSq work2893.out = true := by decide +kernel

def cell2893 : CellCertificate where
  tauBall := tau2893
  contactCenter := center2893
  contactBall := contact2893
  work := work2893
  center_sq := center_sq2893
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2893.1
  jac_ok := checks2893.2.1
  accepted := checks2893.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361


