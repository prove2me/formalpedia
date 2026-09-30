-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0319
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0319
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:09:52.282597+00:00
-- url     : https://prove2.me/theorems/92b25941-cbac-4085-8cf0-c816b021513d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0319` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0319` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0319` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0319 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0319.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0319 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0319

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2552 : RatBall :=
  ⟨⟨67/320, 21/64⟩, 3/640⟩
def center2552 : GaussianRat :=
  ⟨79717703/500000000, 224213933/1000000000⟩
def contact2552 : RatBall := localContactBall tau2552 center2552
def work2552 : RoundedTauEval :=
  evalTau precision tau2552 contact2552 logTwoBall

theorem center_sq2552 : (center2552.re : ℝ)^2 +
    (center2552.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2552]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2552 : work2552.theta.ok = true ∧
    work2552.jac.invOK = true ∧ acceptsUnitSq work2552.out = true := by decide +kernel

def cell2552 : CellCertificate where
  tauBall := tau2552
  contactCenter := center2552
  contactBall := contact2552
  work := work2552
  center_sq := center_sq2552
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2552.1
  jac_ok := checks2552.2.1
  accepted := checks2552.2.2

def tau2553 : RatBall :=
  ⟨⟨13/64, 107/320⟩, 3/640⟩
def center2553 : GaussianRat :=
  ⟨77788111/500000000, 229460827/1000000000⟩
def contact2553 : RatBall := localContactBall tau2553 center2553
def work2553 : RoundedTauEval :=
  evalTau precision tau2553 contact2553 logTwoBall

theorem center_sq2553 : (center2553.re : ℝ)^2 +
    (center2553.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2553]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2553 : work2553.theta.ok = true ∧
    work2553.jac.invOK = true ∧ acceptsUnitSq work2553.out = true := by decide +kernel

def cell2553 : CellCertificate where
  tauBall := tau2553
  contactCenter := center2553
  contactBall := contact2553
  work := work2553
  center_sq := center_sq2553
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2553.1
  jac_ok := checks2553.2.1
  accepted := checks2553.2.2

def tau2554 : RatBall :=
  ⟨⟨67/320, 107/320⟩, 3/640⟩
def center2554 : GaussianRat :=
  ⟨160137389/1000000000, 228757569/1000000000⟩
def contact2554 : RatBall := localContactBall tau2554 center2554
def work2554 : RoundedTauEval :=
  evalTau precision tau2554 contact2554 logTwoBall

theorem center_sq2554 : (center2554.re : ℝ)^2 +
    (center2554.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2554]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2554 : work2554.theta.ok = true ∧
    work2554.jac.invOK = true ∧ acceptsUnitSq work2554.out = true := by decide +kernel

def cell2554 : CellCertificate where
  tauBall := tau2554
  contactCenter := center2554
  contactBall := contact2554
  work := work2554
  center_sq := center_sq2554
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2554.1
  jac_ok := checks2554.2.1
  accepted := checks2554.2.2

def tau2555 : RatBall :=
  ⟨⟨69/320, 21/64⟩, 3/640⟩
def center2555 : GaussianRat :=
  ⟨81980819/500000000, 223513477/1000000000⟩
def contact2555 : RatBall := localContactBall tau2555 center2555
def work2555 : RoundedTauEval :=
  evalTau precision tau2555 contact2555 logTwoBall

theorem center_sq2555 : (center2555.re : ℝ)^2 +
    (center2555.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2555]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2555 : work2555.theta.ok = true ∧
    work2555.jac.invOK = true ∧ acceptsUnitSq work2555.out = true := by decide +kernel

def cell2555 : CellCertificate where
  tauBall := tau2555
  contactCenter := center2555
  contactBall := contact2555
  work := work2555
  center_sq := center_sq2555
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2555.1
  jac_ok := checks2555.2.1
  accepted := checks2555.2.2

def tau2556 : RatBall :=
  ⟨⟨71/320, 21/64⟩, 3/640⟩
def center2556 : GaussianRat :=
  ⟨168468823/1000000000, 55699379/250000000⟩
def contact2556 : RatBall := localContactBall tau2556 center2556
def work2556 : RoundedTauEval :=
  evalTau precision tau2556 contact2556 logTwoBall

theorem center_sq2556 : (center2556.re : ℝ)^2 +
    (center2556.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2556]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2556 : work2556.theta.ok = true ∧
    work2556.jac.invOK = true ∧ acceptsUnitSq work2556.out = true := by decide +kernel

def cell2556 : CellCertificate where
  tauBall := tau2556
  contactCenter := center2556
  contactBall := contact2556
  work := work2556
  center_sq := center_sq2556
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2556.1
  jac_ok := checks2556.2.1
  accepted := checks2556.2.2

def tau2557 : RatBall :=
  ⟨⟨69/320, 107/320⟩, 3/640⟩
def center2557 : GaussianRat :=
  ⟨20584937/125000000, 228038057/1000000000⟩
def contact2557 : RatBall := localContactBall tau2557 center2557
def work2557 : RoundedTauEval :=
  evalTau precision tau2557 contact2557 logTwoBall

theorem center_sq2557 : (center2557.re : ℝ)^2 +
    (center2557.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2557]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2557 : work2557.theta.ok = true ∧
    work2557.jac.invOK = true ∧ acceptsUnitSq work2557.out = true := by decide +kernel

def cell2557 : CellCertificate where
  tauBall := tau2557
  contactCenter := center2557
  contactBall := contact2557
  work := work2557
  center_sq := center_sq2557
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2557.1
  jac_ok := checks2557.2.1
  accepted := checks2557.2.2

def tau2558 : RatBall :=
  ⟨⟨73/320, 21/64⟩, 3/640⟩
def center2558 : GaussianRat :=
  ⟨172956611/1000000000, 222066431/1000000000⟩
def contact2558 : RatBall := localContactBall tau2558 center2558
def work2558 : RoundedTauEval :=
  evalTau precision tau2558 contact2558 logTwoBall

theorem center_sq2558 : (center2558.re : ℝ)^2 +
    (center2558.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2558]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2558 : work2558.theta.ok = true ∧
    work2558.jac.invOK = true ∧ acceptsUnitSq work2558.out = true := by decide +kernel

def cell2558 : CellCertificate where
  tauBall := tau2558
  contactCenter := center2558
  contactBall := contact2558
  work := work2558
  center_sq := center_sq2558
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2558.1
  jac_ok := checks2558.2.1
  accepted := checks2558.2.2

def tau2559 : RatBall :=
  ⟨⟨81/320, 97/320⟩, 3/640⟩
def center2559 : GaussianRat :=
  ⟨469233/2500000, 201515067/1000000000⟩
def contact2559 : RatBall := localContactBall tau2559 center2559
def work2559 : RoundedTauEval :=
  evalTau precision tau2559 contact2559 logTwoBall

theorem center_sq2559 : (center2559.re : ℝ)^2 +
    (center2559.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2559]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2559 : work2559.theta.ok = true ∧
    work2559.jac.invOK = true ∧ acceptsUnitSq work2559.out = true := by decide +kernel

def cell2559 : CellCertificate where
  tauBall := tau2559
  contactCenter := center2559
  contactBall := contact2559
  work := work2559
  center_sq := center_sq2559
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2559.1
  jac_ok := checks2559.2.1
  accepted := checks2559.2.2

def cells : List CellCertificate := [cell2552, cell2553, cell2554, cell2555, cell2556, cell2557, cell2558, cell2559]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0319

end


