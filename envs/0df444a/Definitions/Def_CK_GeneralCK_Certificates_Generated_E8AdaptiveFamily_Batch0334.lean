-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0334
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0334
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:08:08.925873+00:00
-- url     : https://prove2.me/theorems/e0809b6d-8ab8-42f3-b1b4-3823d886cb10
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0334` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0334` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0334` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0334 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0334.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0334 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0334

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2672 : RatBall :=
  ⟨⟨-93/640, -233/640⟩, 3/1280⟩
def center2672 : GaussianRat :=
  ⟨-115220153/1000000000, -257805963/1000000000⟩
def contact2672 : RatBall := localContactBall tau2672 center2672
def work2672 : RoundedTauEval :=
  evalTau precision tau2672 contact2672 logTwoBall

theorem center_sq2672 : (center2672.re : ℝ)^2 +
    (center2672.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2672]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2672 : work2672.theta.ok = true ∧
    work2672.jac.invOK = true ∧ acceptsUnitSq work2672.out = true := by decide +kernel

def cell2672 : CellCertificate where
  tauBall := tau2672
  contactCenter := center2672
  contactBall := contact2672
  work := work2672
  center_sq := center_sq2672
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2672.1
  jac_ok := checks2672.2.1
  accepted := checks2672.2.2

def tau2673 : RatBall :=
  ⟨⟨-91/640, -47/128⟩, 3/1280⟩
def center2673 : GaussianRat :=
  ⟨-14137597/125000000, -260521763/1000000000⟩
def contact2673 : RatBall := localContactBall tau2673 center2673
def work2673 : RoundedTauEval :=
  evalTau precision tau2673 contact2673 logTwoBall

theorem center_sq2673 : (center2673.re : ℝ)^2 +
    (center2673.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2673]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2673 : work2673.theta.ok = true ∧
    work2673.jac.invOK = true ∧ acceptsUnitSq work2673.out = true := by decide +kernel

def cell2673 : CellCertificate where
  tauBall := tau2673
  contactCenter := center2673
  contactBall := contact2673
  work := work2673
  center_sq := center_sq2673
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2673.1
  jac_ok := checks2673.2.1
  accepted := checks2673.2.2

def tau2674 : RatBall :=
  ⟨⟨-89/640, -47/128⟩, 3/1280⟩
def center2674 : GaussianRat :=
  ⟨-110676327/1000000000, -2037627/7812500⟩
def contact2674 : RatBall := localContactBall tau2674 center2674
def work2674 : RoundedTauEval :=
  evalTau precision tau2674 contact2674 logTwoBall

theorem center_sq2674 : (center2674.re : ℝ)^2 +
    (center2674.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2674]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2674 : work2674.theta.ok = true ∧
    work2674.jac.invOK = true ∧ acceptsUnitSq work2674.out = true := by decide +kernel

def cell2674 : CellCertificate where
  tauBall := tau2674
  contactCenter := center2674
  contactBall := contact2674
  work := work2674
  center_sq := center_sq2674
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2674.1
  jac_ok := checks2674.2.1
  accepted := checks2674.2.2

def tau2675 : RatBall :=
  ⟨⟨-91/640, -233/640⟩, 3/1280⟩
def center2675 : GaussianRat :=
  ⟨-112805403/1000000000, -25810217/100000000⟩
def contact2675 : RatBall := localContactBall tau2675 center2675
def work2675 : RoundedTauEval :=
  evalTau precision tau2675 contact2675 logTwoBall

theorem center_sq2675 : (center2675.re : ℝ)^2 +
    (center2675.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2675]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2675 : work2675.theta.ok = true ∧
    work2675.jac.invOK = true ∧ acceptsUnitSq work2675.out = true := by decide +kernel

def cell2675 : CellCertificate where
  tauBall := tau2675
  contactCenter := center2675
  contactBall := contact2675
  work := work2675
  center_sq := center_sq2675
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2675.1
  jac_ok := checks2675.2.1
  accepted := checks2675.2.2

def tau2676 : RatBall :=
  ⟨⟨-89/640, -233/640⟩, 3/1280⟩
def center2676 : GaussianRat :=
  ⟨-22077337/200000000, -258392707/1000000000⟩
def contact2676 : RatBall := localContactBall tau2676 center2676
def work2676 : RoundedTauEval :=
  evalTau precision tau2676 contact2676 logTwoBall

theorem center_sq2676 : (center2676.re : ℝ)^2 +
    (center2676.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2676]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2676 : work2676.theta.ok = true ∧
    work2676.jac.invOK = true ∧ acceptsUnitSq work2676.out = true := by decide +kernel

def cell2676 : CellCertificate where
  tauBall := tau2676
  contactCenter := center2676
  contactBall := contact2676
  work := work2676
  center_sq := center_sq2676
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2676.1
  jac_ok := checks2676.2.1
  accepted := checks2676.2.2

def tau2677 : RatBall :=
  ⟨⟨-87/640, -239/640⟩, 3/1280⟩
def center2677 : GaussianRat :=
  ⟨-4353093/40000000, -53195483/200000000⟩
def contact2677 : RatBall := localContactBall tau2677 center2677
def work2677 : RoundedTauEval :=
  evalTau precision tau2677 contact2677 logTwoBall

theorem center_sq2677 : (center2677.re : ℝ)^2 +
    (center2677.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2677]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2677 : work2677.theta.ok = true ∧
    work2677.jac.invOK = true ∧ acceptsUnitSq work2677.out = true := by decide +kernel

def cell2677 : CellCertificate where
  tauBall := tau2677
  contactCenter := center2677
  contactBall := contact2677
  work := work2677
  center_sq := center_sq2677
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2677.1
  jac_ok := checks2677.2.1
  accepted := checks2677.2.2

def tau2678 : RatBall :=
  ⟨⟨-17/128, -239/640⟩, 3/1280⟩
def center2678 : GaussianRat :=
  ⟨-10638319/100000000, -266268043/1000000000⟩
def contact2678 : RatBall := localContactBall tau2678 center2678
def work2678 : RoundedTauEval :=
  evalTau precision tau2678 contact2678 logTwoBall

theorem center_sq2678 : (center2678.re : ℝ)^2 +
    (center2678.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2678]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2678 : work2678.theta.ok = true ∧
    work2678.jac.invOK = true ∧ acceptsUnitSq work2678.out = true := by decide +kernel

def cell2678 : CellCertificate where
  tauBall := tau2678
  contactCenter := center2678
  contactBall := contact2678
  work := work2678
  center_sq := center_sq2678
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2678.1
  jac_ok := checks2678.2.1
  accepted := checks2678.2.2

def tau2679 : RatBall :=
  ⟨⟨-87/640, -237/640⟩, 3/1280⟩
def center2679 : GaussianRat :=
  ⟨-108535671/1000000000, -263538231/1000000000⟩
def contact2679 : RatBall := localContactBall tau2679 center2679
def work2679 : RoundedTauEval :=
  evalTau precision tau2679 contact2679 logTwoBall

theorem center_sq2679 : (center2679.re : ℝ)^2 +
    (center2679.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2679]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2679 : work2679.theta.ok = true ∧
    work2679.jac.invOK = true ∧ acceptsUnitSq work2679.out = true := by decide +kernel

def cell2679 : CellCertificate where
  tauBall := tau2679
  contactCenter := center2679
  contactBall := contact2679
  work := work2679
  center_sq := center_sq2679
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2679.1
  jac_ok := checks2679.2.1
  accepted := checks2679.2.2

def cells : List CellCertificate := [cell2672, cell2673, cell2674, cell2675, cell2676, cell2677, cell2678, cell2679]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0334

end


