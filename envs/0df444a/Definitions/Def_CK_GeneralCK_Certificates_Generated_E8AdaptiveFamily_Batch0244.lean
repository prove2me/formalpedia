-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0244
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0244
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:49:18.981997+00:00
-- url     : https://prove2.me/theorems/34018fad-1b6a-4683-b770-af0e498c0633
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0244` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0244` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0244` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0244 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0244.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0244 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0244

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1952 : RatBall :=
  ⟨⟨-17/64, 93/320⟩, 3/640⟩
def center1952 : GaussianRat :=
  ⟨-97455589/500000000, 191473909/1000000000⟩
def contact1952 : RatBall := localContactBall tau1952 center1952
def work1952 : RoundedTauEval :=
  evalTau precision tau1952 contact1952 logTwoBall

theorem center_sq1952 : (center1952.re : ℝ)^2 +
    (center1952.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1952]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1952 : work1952.theta.ok = true ∧
    work1952.jac.invOK = true ∧ acceptsUnitSq work1952.out = true := by decide +kernel

def cell1952 : CellCertificate where
  tauBall := tau1952
  contactCenter := center1952
  contactBall := contact1952
  work := work1952
  center_sq := center_sq1952
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1952.1
  jac_ok := checks1952.2.1
  accepted := checks1952.2.2

def tau1953 : RatBall :=
  ⟨⟨-87/320, 19/64⟩, 3/640⟩
def center1953 : GaussianRat :=
  ⟨-199903813/1000000000, 195040739/1000000000⟩
def contact1953 : RatBall := localContactBall tau1953 center1953
def work1953 : RoundedTauEval :=
  evalTau precision tau1953 contact1953 logTwoBall

theorem center_sq1953 : (center1953.re : ℝ)^2 +
    (center1953.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1953]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1953 : work1953.theta.ok = true ∧
    work1953.jac.invOK = true ∧ acceptsUnitSq work1953.out = true := by decide +kernel

def cell1953 : CellCertificate where
  tauBall := tau1953
  contactCenter := center1953
  contactBall := contact1953
  work := work1953
  center_sq := center_sq1953
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1953.1
  jac_ok := checks1953.2.1
  accepted := checks1953.2.2

def tau1954 : RatBall :=
  ⟨⟨-17/64, 19/64⟩, 3/640⟩
def center1954 : GaussianRat :=
  ⟨-39123719/200000000, 48940869/250000000⟩
def contact1954 : RatBall := localContactBall tau1954 center1954
def work1954 : RoundedTauEval :=
  evalTau precision tau1954 contact1954 logTwoBall

theorem center_sq1954 : (center1954.re : ℝ)^2 +
    (center1954.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1954]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1954 : work1954.theta.ok = true ∧
    work1954.jac.invOK = true ∧ acceptsUnitSq work1954.out = true := by decide +kernel

def cell1954 : CellCertificate where
  tauBall := tau1954
  contactCenter := center1954
  contactBall := contact1954
  work := work1954
  center_sq := center_sq1954
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1954.1
  jac_ok := checks1954.2.1
  accepted := checks1954.2.2

def tau1955 : RatBall :=
  ⟨⟨-83/320, 93/320⟩, 3/640⟩
def center1955 : GaussianRat :=
  ⟨-95308733/500000000, 192166077/1000000000⟩
def contact1955 : RatBall := localContactBall tau1955 center1955
def work1955 : RoundedTauEval :=
  evalTau precision tau1955 contact1955 logTwoBall

theorem center_sq1955 : (center1955.re : ℝ)^2 +
    (center1955.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1955]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1955 : work1955.theta.ok = true ∧
    work1955.jac.invOK = true ∧ acceptsUnitSq work1955.out = true := by decide +kernel

def cell1955 : CellCertificate where
  tauBall := tau1955
  contactCenter := center1955
  contactBall := contact1955
  work := work1955
  center_sq := center_sq1955
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1955.1
  jac_ok := checks1955.2.1
  accepted := checks1955.2.2

def tau1956 : RatBall :=
  ⟨⟨-81/320, 93/320⟩, 3/640⟩
def center1956 : GaussianRat :=
  ⟨-93152319/500000000, 24105877/125000000⟩
def contact1956 : RatBall := localContactBall tau1956 center1956
def work1956 : RoundedTauEval :=
  evalTau precision tau1956 contact1956 logTwoBall

theorem center_sq1956 : (center1956.re : ℝ)^2 +
    (center1956.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1956]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1956 : work1956.theta.ok = true ∧
    work1956.jac.invOK = true ∧ acceptsUnitSq work1956.out = true := by decide +kernel

def cell1956 : CellCertificate where
  tauBall := tau1956
  contactCenter := center1956
  contactBall := contact1956
  work := work1956
  center_sq := center_sq1956
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1956.1
  jac_ok := checks1956.2.1
  accepted := checks1956.2.2

def tau1957 : RatBall :=
  ⟨⟨-83/320, 19/64⟩, 3/640⟩
def center1957 : GaussianRat :=
  ⟨-191313683/1000000000, 3929501/20000000⟩
def contact1957 : RatBall := localContactBall tau1957 center1957
def work1957 : RoundedTauEval :=
  evalTau precision tau1957 contact1957 logTwoBall

theorem center_sq1957 : (center1957.re : ℝ)^2 +
    (center1957.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1957]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1957 : work1957.theta.ok = true ∧
    work1957.jac.invOK = true ∧ acceptsUnitSq work1957.out = true := by decide +kernel

def cell1957 : CellCertificate where
  tauBall := tau1957
  contactCenter := center1957
  contactBall := contact1957
  work := work1957
  center_sq := center_sq1957
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1957.1
  jac_ok := checks1957.2.1
  accepted := checks1957.2.2

def tau1958 : RatBall :=
  ⟨⟨-81/320, 19/64⟩, 3/640⟩
def center1958 : GaussianRat :=
  ⟨-186989333/1000000000, 49293783/250000000⟩
def contact1958 : RatBall := localContactBall tau1958 center1958
def work1958 : RoundedTauEval :=
  evalTau precision tau1958 contact1958 logTwoBall

theorem center_sq1958 : (center1958.re : ℝ)^2 +
    (center1958.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1958]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1958 : work1958.theta.ok = true ∧
    work1958.jac.invOK = true ∧ acceptsUnitSq work1958.out = true := by decide +kernel

def cell1958 : CellCertificate where
  tauBall := tau1958
  contactCenter := center1958
  contactBall := contact1958
  work := work1958
  center_sq := center_sq1958
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1958.1
  jac_ok := checks1958.2.1
  accepted := checks1958.2.2

def tau1959 : RatBall :=
  ⟨⟨-79/320, 89/320⟩, 3/640⟩
def center1959 : GaussianRat :=
  ⟨-22585333/125000000, 184857737/1000000000⟩
def contact1959 : RatBall := localContactBall tau1959 center1959
def work1959 : RoundedTauEval :=
  evalTau precision tau1959 contact1959 logTwoBall

theorem center_sq1959 : (center1959.re : ℝ)^2 +
    (center1959.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1959]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1959 : work1959.theta.ok = true ∧
    work1959.jac.invOK = true ∧ acceptsUnitSq work1959.out = true := by decide +kernel

def cell1959 : CellCertificate where
  tauBall := tau1959
  contactCenter := center1959
  contactBall := contact1959
  work := work1959
  center_sq := center_sq1959
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1959.1
  jac_ok := checks1959.2.1
  accepted := checks1959.2.2

def cells : List CellCertificate := [cell1952, cell1953, cell1954, cell1955, cell1956, cell1957, cell1958, cell1959]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0244

end


