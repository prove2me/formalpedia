-- Prove2me | Definitions.Def_QuantumLTF_Majority_AdversaryModel
-- name    : QuantumLTF_Majority_AdversaryModel
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-16T10:59:11.862208+00:00
-- url     : https://prove2.me/theorems/9a841317-66ca-42c2-b0a4-4436ff716f55
-- title:
--   Krawtchouk and adversary model for learning Majority
-- statement:
--   Exact and bounded hidden-support domains, binary Krawtchouk transforms, the dual adversary feasibility and cost predicates, and the explicit lower-bound adversary matrix used throughout Section 4.
-- source:
--   Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Section 4, pp.39–56 and Appendix C.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Majority_oracle

namespace QuantumLTF.Majority

open QAlgorithms

abbrev ExactSupports (n k : ℕ) := {A : Finset (Fin n) // A.card = k}
abbrev BoundedSupports (n k : ℕ) := {A : Finset (Fin n) // A.Nonempty ∧ A.card ≤ k}

def intersectionIndex {n k : ℕ} (A : ExactSupports n k) (S : Qubits n) : Fin (k + 1) :=
  ⟨(A.1.filter fun i => S i).card, by
    have h := Finset.card_filter_le (s := A.1) (p := fun i => S i)
    rw [A.2] at h
    omega⟩

/-- Binary Krawtchouk polynomial evaluated at an integer point. -/
def krawtchouk (k t a : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (t + 1),
    (-1 : ℤ) ^ j * (a.choose j : ℤ) * ((k - a).choose (t - j) : ℤ)

/-- The intersection-free Krawtchouk transform used in Section 4.2. -/
noncomputable def intersectionTransform (k : ℕ) (p q : Fin (k + 1) → ℝ) (a : Fin (k + 1)) : ℝ :=
  ∑ t : Fin (k + 1), (krawtchouk k t a : ℝ) * (p t + (-1 : ℝ) ^ (t : ℕ) * q t)

/-- Feasibility condition for the dual adversary SDP, on a finite hidden-support domain. -/
def DualFeasible {n : ℕ} {ι : Type*} [Fintype ι]
    (support : ι → Finset (Fin n)) (X : Qubits n → Matrix ι ι ℝ) : Prop :=
  (∀ S, Matrix.PosSemidef (X S)) ∧
  ∀ A B, A ≠ B →
    ∑ S : Qubits n, (if majorityBit (support A) S ≠ majorityBit (support B) S
      then X S A B else 0) = 1

/-- A uniform diagonal upper bound on the objective of a dual adversary solution. -/
def DualCostAtMost {n : ℕ} {ι : Type*} [Fintype ι]
    (X : Qubits n → Matrix ι ι ℝ) (T : ℝ) : Prop :=
  ∀ A, ∑ S : Qubits n, X S A A ≤ T

/-- The nonnegative adversary matrix of Eq. (128), indexed by `m`-subsets of a known universe. -/
noncomputable def lowerAdversary {n m : ℕ} (U : Finset (Fin n))
    (A B : {A : Finset (Fin n) // A ⊆ U ∧ A.card = m}) : ℝ :=
  if A = B then 0 else 1 / ((A.1 \ B.1).card : ℝ) / (m.choose (A.1 \ B.1).card : ℝ) ^ 2

/-- Query-difference mask for a Boolean query string. -/
def queryDifference {n : ℕ} {ι : Type*} (support : ι → Finset (Fin n))
    (S : Qubits n) (A B : ι) : ℝ :=
  if majorityBit (support A) S ≠ majorityBit (support B) S then 1 else 0

end QuantumLTF.Majority


