-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementN
-- name    : Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementN
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:28:15.491727+00:00
-- url     : https://prove2.me/theorems/830644fb-2a3e-4767-8c94-8a2fcb81d111
-- title:
--   Statement N
-- statement:
--   Definitions and structural lemmas for Statement N, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/StatementN.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.BranchingDimensions
def Consequences : Prop :=
  ∀ (r K Ns p E0 mS : ℕ) (a Y Q : ℝ), 2 ≤ r → 4 * r ≤ Ns → 13 ≤ p → 1 ≤ Y → 1 ≤ Q →
    1088 * (Ns : ℝ) ^ 2 * Real.log a ≤ ((r + K : ℕ) : ℝ) →
    32 * p * Y * ((r + K : ℕ) : ℝ) ^ 2 * Ns * Q ^ 2 * ((E0 : ℝ) + mS + 1) ≤ a →
    8 ≤ Ns ∧ 416 ≤ a ∧ 1 ≤ Real.log a ∧ 1088 * Ns ^ 2 ≤ r + K ∧
    160 * (Ns : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 * Y ∧ 5 * Ns ≤ r + K ∧ 32 * Y ≤ a ∧ 8 * (Ns : ℝ) ≤ a ∧
    32 * (E0 : ℝ) ≤ a ∧ r + K ≤ 2 * (K - 2 * Ns) ∧ Ns + r ≤ K
def PowMulFloorDivLe : Prop :=
  ∀ (p k Dt Do ao : ℕ) (a Y : ℝ), 1 ≤ p → 1 ≤ k → 0 < Y → Dt ≤ Do → (ao : ℝ) ≤ 2 * a →
    (p : ℝ) ^ Dt * (⌊((ao : ℝ) / (p : ℝ) ^ Do) / ((k : ℝ) ^ 2 * Y)⌋₊ : ℝ) ≤ 2 * a / ((k : ℝ) ^ 2 * Y)
def ReducedDegree : Prop :=
  ∀ (k Ns : ℕ) (a Y at' E' E0 Et : ℝ), 0 < Y → 1 ≤ k → 0 ≤ a → E' ≤ E0 → 32 * E0 ≤ a →
    Et ≤ 4 * Ns * a / ((k : ℝ) ^ 2 * Y) → 160 * (Ns : ℝ) ≤ (k : ℝ) ^ 2 * Y → a ≤ at' →
    (9 / 10 : ℝ) * at' ≤ at' - E' - Et
def CoarseExponentLowerBounds : Prop :=
  ∀ (p k Ns E0 mS R : ℕ) (a Y Q P1 : ℝ), 2 ≤ p → 1 ≤ k → 1 ≤ Ns → 1 ≤ Y → 1 ≤ P1 → P1 ≤ Q →
    32 * p * Y * (k : ℝ) ^ 2 * Ns * Q ^ 2 * ((E0 : ℝ) + mS + 1) ≤ a →
    a / (8 * Y * (k : ℝ) ^ 2 * Ns * P1) < (p : ℝ) ^ (R + 1) →
    4 * Q * ((E0 : ℝ) + mS + 1) < (p : ℝ) ^ R ∧ 1 ≤ R ∧ (mS : ℝ) < (p : ℝ) ^ R
def CoarseScaleBounds : Prop :=
  ∀ (p k Ns D R : ℕ) (a Y P1 at' a' : ℝ), 1 ≤ p → 1 ≤ k → 1 ≤ Ns → 0 < Y → 0 < P1 →
    (p : ℝ) ^ R ≤ a / (8 * Y * (k : ℝ) ^ 2 * Ns * P1) → (p : ℝ) ^ D ≤ P1 → a ≤ at' → (9 / 10 : ℝ) * at' ≤ a' →
    8 * Y * (k : ℝ) ^ 2 * Ns ≤ at' / (p : ℝ) ^ (D + R) ∧ 7.2 * Y * (k : ℝ) ^ 2 * Ns ≤ a' / (p : ℝ) ^ (D + R)
def CoarseExponentCompare : Prop :=
  ∀ (p k Ns D1 L1 R R' dn : ℕ) (a Y P1 : ℝ), 2 ≤ p → 1 ≤ k → 1 ≤ Ns → 0 < Y → 0 < a →
    a / (8 * p * Y * (k : ℝ) ^ 2 * Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ dn)) < (p : ℝ) ^ R' →
    (p : ℝ) ^ R ≤ a / (8 * Y * (k : ℝ) ^ 2 * Ns * P1) → (p : ℝ) ^ (D1 + L1 + 1) ≤ P1 →
    (p : ℝ) ^ L1 < (p : ℝ) ^ dn * (p : ℝ) ^ R' / (p : ℝ) ^ R ∧ R + L1 < dn + R'
def CyclicProductRatio : Prop :=
  ∀ (J : ℕ) [NeZero J] (Qs ρ : Fin J → ℝ), (∀ j, ρ j ≠ 0) →
    ∏ j : Fin J, (Qs (j + 1) * ρ (j + 1) / ρ j) = ∏ j : Fin J, Qs j
def BackThreshold : Prop :=
  ∀ (k r Ns : ℕ) (Y co th : ℝ), 3 ≤ k → r ≤ k → 8 ≤ Ns → 1 ≤ Y → 8 * Y * (k : ℝ) ^ 2 * Ns ≤ co →
    (2 / 3 : ℝ) * (0.9 * co - ((k : ℝ) + r + 2) - ((k : ℝ) * Ns + 1)) ≤ th →
    co / 2 ≤ th - (k : ℝ) * Ns
def BackMargin : Prop :=
  ∀ (k Ns : ℕ) (pR nu ka dS dV mS s : ℝ), 0 < pR → ka + ((k : ℝ) * Ns + 1) ≤ nu → dS + dV < (k : ℝ) * Ns * pR →
    mS < pR → (pR * ka + dV) + mS + s < pR * nu - dS + s
def OrderBounds : Prop :=
  ∀ (p k Ns D Do L1 R : ℕ) (a Y P1 La : ℝ), 2 ≤ p → 1 ≤ k → 1 ≤ Ns → 1 ≤ Y → 0 ≤ a → 0 ≤ La →
    (p : ℝ) ^ R ≤ a / (8 * Y * (k : ℝ) ^ 2 * Ns * P1) → (p : ℝ) ^ (D + L1 + 1) ≤ P1 → D + L1 + 1 ≤ Do →
    (k : ℝ) * (p : ℝ) ^ R ≤ a / (p : ℝ) ^ (L1 + D + 1) / (8 * Y * k * Ns) ∧
    (p : ℝ) ^ R * (La * a / (p * k * (p : ℝ) ^ (D + R))) + k * (p : ℝ) ^ R ≤
      La * a / (p * k * (p : ℝ) ^ D) + a / (p : ℝ) ^ (L1 + D) ∧
    (p : ℝ) ^ R * (La * a / (p * k * (p : ℝ) ^ (D + R)) + 4 * a / (p : ℝ) ^ (Do + R)) + k * (p : ℝ) ^ R ≤
      La * a / (p * k * (p : ℝ) ^ D) + 10 * a / (p : ℝ) ^ (L1 + D)
def DegreeBound : Prop :=
  ∀ (p k L1 N : ℕ) (a La Q : ℝ) (D : Fin N → ℕ) (o lab : Fin N → ℝ), 1 ≤ p → 1 ≤ k → 0 ≤ a → 0 ≤ La →
    (∀ z, (p : ℝ) ^ D z ≤ Q) →
    (∀ z, o z ≤ La * a / (p * k * (p : ℝ) ^ D z) + 10 * a / (p : ℝ) ^ (L1 + D z)) →
    (∀ z, lab z ≤ k * (p : ℝ) ^ D z) →
    ∑ z, ((p : ℝ) ^ D z * o z + lab z) ≤ N * (La * a / (p * k) + 10 * a / (p : ℝ) ^ L1 + k * Q)
def AdmissibleFloor : Prop :=
  ∀ (k r Ns : ℕ) (a Y c : ℝ) (B : ℤ), 10 ≤ k → r ≤ k → 8 ≤ Ns → 1 ≤ Y → 7.2 * Y * (k : ℝ) ^ 2 * Ns ≤ c → c ≤ 2 * a →
    (B = ⌊c⌋ - ((k : ℤ) + r + 1) - ((k : ℤ) * Ns + 1) ∨ (c - k < (B : ℝ) ∧ (B : ℝ) ≤ c)) →
    c - 2 * k * Ns ≤ (B : ℝ) ∧ (B : ℝ) ≤ c ∧ 7 * Y * (k : ℝ) ^ 2 * Ns ≤ (B : ℝ) ∧ (k : ℝ) ≤ (B : ℝ) ∧ (B : ℝ) ≤ 2 * a
def AdmissibleRatio : Prop :=
  ∀ (p k Ns D D' R : ℕ) (a Y a1 a2 B B' : ℝ), 2 ≤ p → 10 ≤ k → 1 ≤ Ns → 1 ≤ Y → 0 < a → D' + 2 ≤ D →
    0.9 * a ≤ a1 → a1 ≤ 2 * a → 0.9 * a ≤ a2 → a2 ≤ 2 * a →
    7.2 * Y * (k : ℝ) ^ 2 * Ns ≤ a2 / (p : ℝ) ^ (D' + R) →
    B ≤ a1 / (p : ℝ) ^ (D + R) → a2 / (p : ℝ) ^ (D' + R) - 2 * k * Ns ≤ B' →
    (p : ℝ) ^ 2 * B ≤ 5 * B'
def AdmissibleBoundOfLargerExponent : Prop :=
  ∀ (p D D' R : ℕ) (a a2 B' : ℝ), 1 ≤ p → 0 ≤ a → D + 1 ≤ D' → a2 ≤ 2 * a → B' ≤ a2 / (p : ℝ) ^ (D' + R) →
    B' ≤ 2 * (a / (p : ℝ) ^ (D + R)) / p ∧ 2 * (a / (p : ℝ) ^ (D + R)) / p ≤ 4 * (a / (p : ℝ) ^ (D + R)) / p
def GeomDistinct : Prop :=
  ∀ (p m0 : ℕ) (s : Finset ℕ), 2 ≤ p → (∀ D ∈ s, m0 ≤ D) → ∑ D ∈ s, (1 / (p : ℝ) ^ D) ≤ 2 / (p : ℝ) ^ m0
def AdmissibleSmallRatio : Prop :=
  ∀ (p k Ns D1 L1 R R' : ℕ) (a Y Qn be : ℝ), 2 ≤ p → 1 ≤ k → 1 ≤ Ns → 1 ≤ Y → 0 < a → 0 < Qn → 1 ≤ L1 →
    be ≤ 4 * a / (p : ℝ) ^ (R + D1 + L1 + 1) →
    a / (8 * p * Y * (k : ℝ) ^ 2 * Ns * ((p : ℝ) ^ D1 * Qn)) < (p : ℝ) ^ R' →
    128 * (k : ℝ) ^ 2 * Ns * Y ^ 2 ≤ (p : ℝ) ^ (L1 - 1) →
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) < 32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ∧
    32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ≤ 1 / (4 * p * Y) ∧
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) ≤ 1 / (4 * Y)
def PaddingDegreeBounds : Prop :=
  ∀ (k r : ℕ) (Q' nv e de : ℤ) (c : ℝ), (k : ℤ) < Q' → c - (k : ℝ) / Q' < (nv : ℝ) / Q' → (nv : ℝ) / Q' ≤ c →
    0 ≤ e → e < r * Q' → nv - e = Q' * (de + (⌊c⌋ - ((k : ℤ) + r + 1))) →
    (k : ℤ) < de ∧ de < (k : ℤ) + r + 2
def FinalProduct : Prop :=
  ∀ (J r N Ns k : ℕ) (a Y E0 : ℝ), 2 ≤ r → 3 * J * r ≤ N → 0 < Y → (N : ℝ) * r / Y < 1 → 32 * Y ≤ a → 1 ≤ Ns →
    4 * Ns ≤ k → 0 ≤ E0 → k * E0 / a ≤ 1 / (32 * Y) →
    1 - (N : ℝ) * r / Y ≤
      (1 - (a ^ (Ns ^ 2))⁻¹) ^ J * (1 - 0.28 / Y) ^ (J * r) * (1 - r / (2 * Y)) ^ (J * r) *
        (1 - k * E0 / a - 4 * Ns / (k * Y)) ^ N
end Formalism.InvariantFactorPaths.BranchingDimensions


